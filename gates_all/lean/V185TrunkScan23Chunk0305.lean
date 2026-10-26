import V185TrunkScan23Chunk0304

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1804034 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_1804034 : Nat := 118140960795 + 1804034 * 2 ^ 59
def prefixEnd_1804034 : Nat := 4983230072969 + 3 ^ 40 * 1804034 * 2
def baseEnd_1804034 : Nat := 926336559053299942378405

theorem tailTrace_1804034 : CollatzResearch.WordTrace tailWord_1804034 prefixEnd_1804034 926336559053299942378405 := by
  unfold tailWord_1804034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16449631386575099330714789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43865683697533598215239437 16449631386575099330714789)
  ·
    refine ⟨3084305884982831124509023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16449631386575099330714789 3084305884982831124509023)
    ·
      refine ⟨4626458827474246686763535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3084305884982831124509023 4626458827474246686763535)
      ·
        refine ⟨6939688241211370030145303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4626458827474246686763535 6939688241211370030145303)
        ·
          refine ⟨10409532361817055045217955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939688241211370030145303 10409532361817055045217955)
          ·
            refine ⟨15614298542725582567826933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10409532361817055045217955 15614298542725582567826933)
            ·
              refine ⟨1463840488380523365733775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15614298542725582567826933 1463840488380523365733775)
              ·
                refine ⟨2195760732570785048600663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463840488380523365733775 2195760732570785048600663)
                ·
                  refine ⟨3293641098856177572900995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195760732570785048600663 3293641098856177572900995)
                  ·
                    refine ⟨4940461648284266359351493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3293641098856177572900995 4940461648284266359351493)
                    ·
                      refine ⟨926336559053299942378405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4940461648284266359351493 926336559053299942378405)
                      ·
                        rfl

theorem cell23_1804034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_1804034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804034 prefixEnd_1804034 := by exact prefixLift 1804034
  have htrace : WordTrace (prefixWord ++ tailWord_1804034) baseStart_1804034 baseEnd_1804034 := by
    simpa [prefixWord, tailWord_1804034, baseEnd_1804034] using wordTrace_append hprefix tailTrace_1804034
  have hstable : (prefixWord ++ tailWord_1804034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804034).length < 2 ^ (prefixWord ++ tailWord_1804034).sum := by decide
  have hdescent : baseEnd_1804034 < baseStart_1804034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804053 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_1804053 : Nat := 118140960795 + 1804053 * 2 ^ 59
def prefixEnd_1804053 : Nat := 4983230072969 + 3 ^ 40 * 1804053 * 2
def baseEnd_1804053 : Nat := 308782105061911789346939

theorem tailTrace_1804053 : CollatzResearch.WordTrace tailWord_1804053 prefixEnd_1804053 308782105061911789346939 := by
  unfold tailWord_1804053
  simp only [CollatzResearch.WordTrace]
  refine ⟨65799218533231563567800813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43866145688821042378533875 65799218533231563567800813)
  ·
    refine ⟨24674706949961836337925305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65799218533231563567800813 24674706949961836337925305)
    ·
      refine ⟨18506030212471377253443979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24674706949961836337925305 18506030212471377253443979)
      ·
        refine ⟨27759045318707065880165969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18506030212471377253443979 27759045318707065880165969)
        ·
          refine ⟨20819283989030299410124477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27759045318707065880165969 20819283989030299410124477)
          ·
            refine ⟨7807231495886362278796679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20819283989030299410124477 7807231495886362278796679)
            ·
              refine ⟨11710847243829543418195019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807231495886362278796679 11710847243829543418195019)
              ·
                refine ⟨17566270865744315127292529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11710847243829543418195019 17566270865744315127292529)
                ·
                  refine ⟨13174703149308236345469397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17566270865744315127292529 13174703149308236345469397)
                  ·
                    refine ⟨308782105061911789346939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13174703149308236345469397 308782105061911789346939)
                    ·
                      rfl

theorem cell23_1804053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_1804053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804053 prefixEnd_1804053 := by exact prefixLift 1804053
  have htrace : WordTrace (prefixWord ++ tailWord_1804053) baseStart_1804053 baseEnd_1804053 := by
    simpa [prefixWord, tailWord_1804053, baseEnd_1804053] using wordTrace_append hprefix tailTrace_1804053
  have hstable : (prefixWord ++ tailWord_1804053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804053).length < 2 ^ (prefixWord ++ tailWord_1804053).sum := by decide
  have hdescent : baseEnd_1804053 < baseStart_1804053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804067 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 3]
def baseStart_1804067 : Nat := 118140960795 + 1804067 * 2 ^ 59
def prefixEnd_1804067 : Nat := 4983230072969 + 3 ^ 40 * 1804067 * 2
def baseEnd_1804067 : Nat := 926353503914898313265753

theorem tailTrace_1804067 : CollatzResearch.WordTrace tailWord_1804067 prefixEnd_1804067 926353503914898313265753 := by
  unfold tailWord_1804067
  simp only [CollatzResearch.WordTrace]
  refine ⟨65799729155180843958810455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43866486103453895972540303 65799729155180843958810455)
  ·
    refine ⟨98699593732771265938215683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65799729155180843958810455 98699593732771265938215683)
    ·
      refine ⟨148049390599156898907323525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98699593732771265938215683 148049390599156898907323525)
      ·
        refine ⟨27759260737341918545123161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148049390599156898907323525 27759260737341918545123161)
        ·
          refine ⟨20819445553006438908842371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27759260737341918545123161 20819445553006438908842371)
          ·
            refine ⟨31229168329509658363263557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20819445553006438908842371 31229168329509658363263557)
            ·
              refine ⟨5855469061783060943111917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31229168329509658363263557 5855469061783060943111917)
              ·
                refine ⟨2195800898168647853666969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5855469061783060943111917 2195800898168647853666969)
                ·
                  refine ⟨1646850673626485890250227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2195800898168647853666969 1646850673626485890250227)
                  ·
                    refine ⟨2470276010439728835375341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1646850673626485890250227 2470276010439728835375341)
                    ·
                      refine ⟨926353503914898313265753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2470276010439728835375341 926353503914898313265753)
                      ·
                        rfl

theorem cell23_1804067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_1804067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804067 prefixEnd_1804067 := by exact prefixLift 1804067
  have htrace : WordTrace (prefixWord ++ tailWord_1804067) baseStart_1804067 baseEnd_1804067 := by
    simpa [prefixWord, tailWord_1804067, baseEnd_1804067] using wordTrace_append hprefix tailTrace_1804067
  have hstable : (prefixWord ++ tailWord_1804067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804067).length < 2 ^ (prefixWord ++ tailWord_1804067).sum := by decide
  have hdescent : baseEnd_1804067 < baseStart_1804067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804160 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 2, 5]
def baseStart_1804160 : Nat := 118140960795 + 1804160 * 2 ^ 59
def prefixEnd_1804160 : Nat := 4983230072969 + 3 ^ 40 * 1804160 * 2
def baseEnd_1804160 : Nat := 308800419205255483134275

theorem tailTrace_1804160 : CollatzResearch.WordTrace tailWord_1804160 prefixEnd_1804160 308800419205255483134275 := by
  unfold tailWord_1804160
  simp only [CollatzResearch.WordTrace]
  refine ⟨32901560571921960420972967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43868747429229280561297289 32901560571921960420972967)
  ·
    refine ⟨49352340857882940631459451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32901560571921960420972967 49352340857882940631459451)
    ·
      refine ⟨74028511286824410947189177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49352340857882940631459451 74028511286824410947189177)
      ·
        refine ⟨55521383465118308210391883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74028511286824410947189177 55521383465118308210391883)
        ·
          refine ⟨83282075197677462315587825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55521383465118308210391883 83282075197677462315587825)
          ·
            refine ⟨62461556398258096736690869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83282075197677462315587825 62461556398258096736690869)
            ·
              refine ⟨5855770912336696569064769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62461556398258096736690869 5855770912336696569064769)
              ·
                refine ⟨4391828184252522426798577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5855770912336696569064769 4391828184252522426798577)
                ·
                  refine ⟨3293871138189391820098933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4391828184252522426798577 3293871138189391820098933)
                  ·
                    refine ⟨308800419205255483134275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3293871138189391820098933 308800419205255483134275)
                    ·
                      rfl

theorem cell23_1804160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_1804160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804160 prefixEnd_1804160 := by exact prefixLift 1804160
  have htrace : WordTrace (prefixWord ++ tailWord_1804160) baseStart_1804160 baseEnd_1804160 := by
    simpa [prefixWord, tailWord_1804160, baseEnd_1804160] using wordTrace_append hprefix tailTrace_1804160
  have hstable : (prefixWord ++ tailWord_1804160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804160).length < 2 ^ (prefixWord ++ tailWord_1804160).sum := by decide
  have hdescent : baseEnd_1804160 < baseStart_1804160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804194 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_1804194 : Nat := 118140960795 + 1804194 * 2 ^ 59
def prefixEnd_1804194 : Nat := 4983230072969 + 3 ^ 40 * 1804194 * 2
def baseEnd_1804194 : Nat := 308806238652673105459223

theorem tailTrace_1804194 : CollatzResearch.WordTrace tailWord_1804194 prefixEnd_1804194 308806238652673105459223 := by
  unfold tailWord_1804194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16451090306430186162170909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43869574150480496432455757 16451090306430186162170909)
  ·
    refine ⟨6169158864911319810814091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16451090306430186162170909 6169158864911319810814091)
    ·
      refine ⟨9253738297366979716221137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6169158864911319810814091 9253738297366979716221137)
      ·
        refine ⟨6940303723025234787165853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9253738297366979716221137 6940303723025234787165853)
        ·
          refine ⟨2602613896134463045187195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6940303723025234787165853 2602613896134463045187195)
          ·
            refine ⟨3903920844201694567780793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602613896134463045187195 3903920844201694567780793)
            ·
              refine ⟨2927940633151270925835595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3903920844201694567780793 2927940633151270925835595)
              ·
                refine ⟨4391910949726906388753393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927940633151270925835595 4391910949726906388753393)
                ·
                  refine ⟨3293933212295179791565045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4391910949726906388753393 3293933212295179791565045)
                  ·
                    refine ⟨308806238652673105459223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3293933212295179791565045 308806238652673105459223)
                    ·
                      rfl

theorem cell23_1804194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_1804194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804194 prefixEnd_1804194 := by exact prefixLift 1804194
  have htrace : WordTrace (prefixWord ++ tailWord_1804194) baseStart_1804194 baseEnd_1804194 := by
    simpa [prefixWord, tailWord_1804194, baseEnd_1804194] using wordTrace_append hprefix tailTrace_1804194
  have hstable : (prefixWord ++ tailWord_1804194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804194).length < 2 ^ (prefixWord ++ tailWord_1804194).sum := by decide
  have hdescent : baseEnd_1804194 < baseStart_1804194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804217 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1804217 : Nat := 118140960795 + 1804217 * 2 ^ 59
def prefixEnd_1804217 : Nat := 4983230072969 + 3 ^ 40 * 1804217 * 2
def baseEnd_1804217 : Nat := 926430526013072726390063

theorem tailTrace_1804217 : CollatzResearch.WordTrace tailWord_1804217 prefixEnd_1804217 926430526013072726390063 := by
  unfold tailWord_1804217
  simp only [CollatzResearch.WordTrace]
  refine ⟨65805200104637419576770905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43870133403091613051180603 65805200104637419576770905)
  ·
    refine ⟨49353900078478064682578179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65805200104637419576770905 49353900078478064682578179)
    ·
      refine ⟨74030850117717097023867269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49353900078478064682578179 74030850117717097023867269)
      ·
        refine ⟨13880784397071955691975113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74030850117717097023867269 13880784397071955691975113)
        ·
          refine ⟨10410588297803966768981335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13880784397071955691975113 10410588297803966768981335)
          ·
            refine ⟨15615882446705950153472003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10410588297803966768981335 15615882446705950153472003)
            ·
              refine ⟨23423823670058925230208005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15615882446705950153472003 23423823670058925230208005)
              ·
                refine ⟨4391966938136048480664001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23423823670058925230208005 4391966938136048480664001)
                ·
                  refine ⟨3293975203602036360498001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4391966938136048480664001 3293975203602036360498001)
                  ·
                    refine ⟨2470481402701527270373501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3293975203602036360498001 2470481402701527270373501)
                    ·
                      refine ⟨926430526013072726390063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2470481402701527270373501 926430526013072726390063)
                      ·
                        rfl

theorem cell23_1804217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1804217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804217 prefixEnd_1804217 := by exact prefixLift 1804217
  have htrace : WordTrace (prefixWord ++ tailWord_1804217) baseStart_1804217 baseEnd_1804217 := by
    simpa [prefixWord, tailWord_1804217, baseEnd_1804217] using wordTrace_append hprefix tailTrace_1804217
  have hstable : (prefixWord ++ tailWord_1804217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804217).length < 2 ^ (prefixWord ++ tailWord_1804217).sum := by decide
  have hdescent : baseEnd_1804217 < baseStart_1804217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804224 : List Nat := [2, 1, 1, 2, 3, 2, 3, 4, 1, 4]
def baseStart_1804224 : Nat := 118140960795 + 1804224 * 2 ^ 59
def prefixEnd_1804224 : Nat := 4983230072969 + 3 ^ 40 * 1804224 * 2
def baseEnd_1804224 : Nat := 308811373459218066334177

theorem tailTrace_1804224 : CollatzResearch.WordTrace tailWord_1804224 prefixEnd_1804224 308811373459218066334177 := by
  unfold tailWord_1804224
  simp only [CollatzResearch.WordTrace]
  refine ⟨32902727707806029886137863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43870303610408039848183817 32902727707806029886137863)
  ·
    refine ⟨49354091561709044829206795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32902727707806029886137863 49354091561709044829206795)
    ·
      refine ⟨74031137342563567243810193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49354091561709044829206795 74031137342563567243810193)
      ·
        refine ⟨55523353006922675432857645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74031137342563567243810193 55523353006922675432857645)
        ·
          refine ⟨20821257377596003287321617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55523353006922675432857645 20821257377596003287321617)
          ·
            refine ⟨15615943033197002465491213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20821257377596003287321617 15615943033197002465491213)
            ·
              refine ⟨5855978637448875924559205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15615943033197002465491213 5855978637448875924559205)
              ·
                refine ⟨1097995994521664235854851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5855978637448875924559205 1097995994521664235854851)
                ·
                  refine ⟨1646993991782496353782277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097995994521664235854851 1646993991782496353782277)
                  ·
                    refine ⟨308811373459218066334177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646993991782496353782277 308811373459218066334177)
                    ·
                      rfl

theorem cell23_1804224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 4].length) (baseStart_1804224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804224 prefixEnd_1804224 := by exact prefixLift 1804224
  have htrace : WordTrace (prefixWord ++ tailWord_1804224) baseStart_1804224 baseEnd_1804224 := by
    simpa [prefixWord, tailWord_1804224, baseEnd_1804224] using wordTrace_append hprefix tailTrace_1804224
  have hstable : (prefixWord ++ tailWord_1804224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804224).length < 2 ^ (prefixWord ++ tailWord_1804224).sum := by decide
  have hdescent : baseEnd_1804224 < baseStart_1804224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804280 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 3, 6]
def baseStart_1804280 : Nat := 118140960795 + 1804280 * 2 ^ 59
def prefixEnd_1804280 : Nat := 4983230072969 + 3 ^ 40 * 1804280 * 2
def baseEnd_1804280 : Nat := 308820958431435326634091

theorem tailTrace_1804280 : CollatzResearch.WordTrace tailWord_1804280 prefixEnd_1804280 308820958431435326634091 := by
  unfold tailWord_1804280
  simp only [CollatzResearch.WordTrace]
  refine ⟨32903748951704590668157147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43871665268939454224209529 32903748951704590668157147)
  ·
    refine ⟨49355623427556886002235721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32903748951704590668157147 49355623427556886002235721)
    ·
      refine ⟨37016717570667664501676791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49355623427556886002235721 37016717570667664501676791)
      ·
        refine ⟨55525076356001496752515187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37016717570667664501676791 55525076356001496752515187)
        ·
          refine ⟨83287614534002245128772781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55525076356001496752515187 83287614534002245128772781)
          ·
            refine ⟨31232855450250841923289793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83287614534002245128772781 31232855450250841923289793)
            ·
              refine ⟨23424641587688131442467345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31232855450250841923289793 23424641587688131442467345)
              ·
                refine ⟨17568481190766098581850509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23424641587688131442467345 17568481190766098581850509)
                ·
                  refine ⟨6588180446537286968193941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17568481190766098581850509 6588180446537286968193941)
                  ·
                    refine ⟨308820958431435326634091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6588180446537286968193941 308820958431435326634091)
                    ·
                      rfl

theorem cell23_1804280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_1804280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804280 prefixEnd_1804280 := by exact prefixLift 1804280
  have htrace : WordTrace (prefixWord ++ tailWord_1804280) baseStart_1804280 baseEnd_1804280 := by
    simpa [prefixWord, tailWord_1804280, baseEnd_1804280] using wordTrace_append hprefix tailTrace_1804280
  have hstable : (prefixWord ++ tailWord_1804280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804280).length < 2 ^ (prefixWord ++ tailWord_1804280).sum := by decide
  have hdescent : baseEnd_1804280 < baseStart_1804280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804281 : List Nat := [1, 2, 1, 3, 1, 4, 2, 4, 1, 1, 3]
def baseStart_1804281 : Nat := 118140960795 + 1804281 * 2 ^ 59
def prefixEnd_1804281 : Nat := 4983230072969 + 3 ^ 40 * 1804281 * 2
def baseEnd_1804281 : Nat := 926463388774960475989769

theorem tailTrace_1804281 : CollatzResearch.WordTrace tailWord_1804281 prefixEnd_1804281 926463388774960475989769 := by
  unfold tailWord_1804281
  simp only [CollatzResearch.WordTrace]
  refine ⟨65807534376405558507100697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43871689584270372338067131 65807534376405558507100697)
  ·
    refine ⟨49355650782304168880325523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65807534376405558507100697 49355650782304168880325523)
    ·
      refine ⟨74033476173456253320488285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49355650782304168880325523 74033476173456253320488285)
      ·
        refine ⟨27762553565046094995183107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74033476173456253320488285 27762553565046094995183107)
        ·
          refine ⟨41643830347569142492774661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27762553565046094995183107 41643830347569142492774661)
          ·
            refine ⟨7808218190169214217395249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41643830347569142492774661 7808218190169214217395249)
            ·
              refine ⟨5856163642626910663046437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7808218190169214217395249 5856163642626910663046437)
              ·
                refine ⟨1098030682992545749321207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5856163642626910663046437 1098030682992545749321207)
                ·
                  refine ⟨1647046024488818623981811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098030682992545749321207 1647046024488818623981811)
                  ·
                    refine ⟨2470569036733227935972717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1647046024488818623981811 2470569036733227935972717)
                    ·
                      refine ⟨926463388774960475989769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2470569036733227935972717 926463388774960475989769)
                      ·
                        rfl

theorem cell23_1804281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_1804281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804281 prefixEnd_1804281 := by exact prefixLift 1804281
  have htrace : WordTrace (prefixWord ++ tailWord_1804281) baseStart_1804281 baseEnd_1804281 := by
    simpa [prefixWord, tailWord_1804281, baseEnd_1804281] using wordTrace_append hprefix tailTrace_1804281
  have hstable : (prefixWord ++ tailWord_1804281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804281).length < 2 ^ (prefixWord ++ tailWord_1804281).sum := by decide
  have hdescent : baseEnd_1804281 < baseStart_1804281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804307 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 3]
def baseStart_1804307 : Nat := 118140960795 + 1804307 * 2 ^ 59
def prefixEnd_1804307 : Nat := 4983230072969 + 3 ^ 40 * 1804307 * 2
def baseEnd_1804307 : Nat := 926476739271977374264649

theorem tailTrace_1804307 : CollatzResearch.WordTrace tailWord_1804307 prefixEnd_1804307 926476739271977374264649 := by
  unfold tailWord_1804307
  simp only [CollatzResearch.WordTrace]
  refine ⟨65808482674311364947547175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43872321782874243298364783 65808482674311364947547175)
  ·
    refine ⟨98712724011467047421320763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65808482674311364947547175 98712724011467047421320763)
    ·
      refine ⟨148069086017200571131981145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98712724011467047421320763 148069086017200571131981145)
      ·
        refine ⟨111051814512900428348985859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148069086017200571131981145 111051814512900428348985859)
        ·
          refine ⟨166577721769350642523478789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111051814512900428348985859 166577721769350642523478789)
          ·
            refine ⟨31233322831753245473152273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166577721769350642523478789 31233322831753245473152273)
            ·
              refine ⟨23424992123814934104864205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31233322831753245473152273 23424992123814934104864205)
              ·
                refine ⟨8784372046430600289324077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23424992123814934104864205 8784372046430600289324077)
                ·
                  refine ⟨3294139517411475108496529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8784372046430600289324077 3294139517411475108496529)
                  ·
                    refine ⟨2470604638058606331372397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3294139517411475108496529 2470604638058606331372397)
                    ·
                      refine ⟨926476739271977374264649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2470604638058606331372397 926476739271977374264649)
                      ·
                        rfl

theorem cell23_1804307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_1804307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804307 prefixEnd_1804307 := by exact prefixLift 1804307
  have htrace : WordTrace (prefixWord ++ tailWord_1804307) baseStart_1804307 baseEnd_1804307 := by
    simpa [prefixWord, tailWord_1804307, baseEnd_1804307] using wordTrace_append hprefix tailTrace_1804307
  have hstable : (prefixWord ++ tailWord_1804307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804307).length < 2 ^ (prefixWord ++ tailWord_1804307).sum := by decide
  have hdescent : baseEnd_1804307 < baseStart_1804307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804338 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_1804338 : Nat := 118140960795 + 1804338 * 2 ^ 59
def prefixEnd_1804338 : Nat := 4983230072969 + 3 ^ 40 * 1804338 * 2
def baseEnd_1804338 : Nat := 926492657172266752977007

theorem tailTrace_1804338 : CollatzResearch.WordTrace tailWord_1804338 prefixEnd_1804338 926492657172266752977007 := by
  unfold tailWord_1804338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16452403334299764310481417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43873075558132704827950445 16452403334299764310481417)
  ·
    refine ⟨12339302500724823232861063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16452403334299764310481417 12339302500724823232861063)
    ·
      refine ⟨18508953751087234849291595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12339302500724823232861063 18508953751087234849291595)
      ·
        refine ⟨27763430626630852273937393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18508953751087234849291595 27763430626630852273937393)
        ·
          refine ⟨20822572969973139205453045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27763430626630852273937393 20822572969973139205453045)
          ·
            refine ⟨1952116215934981800511223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20822572969973139205453045 1952116215934981800511223)
            ·
              refine ⟨2928174323902472700766835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952116215934981800511223 2928174323902472700766835)
              ·
                refine ⟨4392261485853709051150253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928174323902472700766835 4392261485853709051150253)
                ·
                  refine ⟨1647098057195140894181345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4392261485853709051150253 1647098057195140894181345)
                  ·
                    refine ⟨1235323542896355670636009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1647098057195140894181345 1235323542896355670636009)
                    ·
                      refine ⟨926492657172266752977007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235323542896355670636009 926492657172266752977007)
                      ·
                        rfl

theorem cell23_1804338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_1804338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804338 prefixEnd_1804338 := by exact prefixLift 1804338
  have htrace : WordTrace (prefixWord ++ tailWord_1804338) baseStart_1804338 baseEnd_1804338 := by
    simpa [prefixWord, tailWord_1804338, baseEnd_1804338] using wordTrace_append hprefix tailTrace_1804338
  have hstable : (prefixWord ++ tailWord_1804338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804338).length < 2 ^ (prefixWord ++ tailWord_1804338).sum := by decide
  have hdescent : baseEnd_1804338 < baseStart_1804338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804407 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_1804407 : Nat := 118140960795 + 1804407 * 2 ^ 59
def prefixEnd_1804407 : Nat := 4983230072969 + 3 ^ 40 * 1804407 * 2
def baseEnd_1804407 : Nat := 926528087337426983014189

theorem tailTrace_1804407 : CollatzResearch.WordTrace tailWord_1804407 prefixEnd_1804407 926528087337426983014189 := by
  unfold tailWord_1804407
  simp only [CollatzResearch.WordTrace]
  refine ⟨65812129973949082026187475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43874753315966054684124983 65812129973949082026187475)
  ·
    refine ⟨98718194960923623039281213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65812129973949082026187475 98718194960923623039281213)
    ·
      refine ⟨37019323110346358639730455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98718194960923623039281213 37019323110346358639730455)
      ·
        refine ⟨55528984665519537959595683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37019323110346358639730455 55528984665519537959595683)
        ·
          refine ⟨83293476998279306939393525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55528984665519537959595683 83293476998279306939393525)
          ·
            refine ⟨7808763468588685025568143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83293476998279306939393525 7808763468588685025568143)
            ·
              refine ⟨11713145202883027538352215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7808763468588685025568143 11713145202883027538352215)
              ·
                refine ⟨17569717804324541307528323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11713145202883027538352215 17569717804324541307528323)
                ·
                  refine ⟨26354576706486811961292485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17569717804324541307528323 26354576706486811961292485)
                  ·
                    refine ⟨4941483132466277242742341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26354576706486811961292485 4941483132466277242742341)
                    ·
                      refine ⟨926528087337426983014189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4941483132466277242742341 926528087337426983014189)
                      ·
                        rfl

theorem cell23_1804407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_1804407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804407 prefixEnd_1804407 := by exact prefixLift 1804407
  have htrace : WordTrace (prefixWord ++ tailWord_1804407) baseStart_1804407 baseEnd_1804407 := by
    simpa [prefixWord, tailWord_1804407, baseEnd_1804407] using wordTrace_append hprefix tailTrace_1804407
  have hstable : (prefixWord ++ tailWord_1804407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804407).length < 2 ^ (prefixWord ++ tailWord_1804407).sum := by decide
  have hdescent : baseEnd_1804407 < baseStart_1804407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804444 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1804444 : Nat := 118140960795 + 1804444 * 2 ^ 59
def prefixEnd_1804444 : Nat := 4983230072969 + 3 ^ 40 * 1804444 * 2
def baseEnd_1804444 : Nat := 926547086121643338251519

theorem tailTrace_1804444 : CollatzResearch.WordTrace tailWord_1804444 prefixEnd_1804444 926547086121643338251519 := by
  unfold tailWord_1804444
  simp only [CollatzResearch.WordTrace]
  refine ⟨32906739737407518672642193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43875652983210024896856257 32906739737407518672642193)
  ·
    refine ⟨24680054803055639004481645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32906739737407518672642193 24680054803055639004481645)
    ·
      refine ⟨9255020551145864626680617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24680054803055639004481645 9255020551145864626680617)
      ·
        refine ⟨6941265413359398470010463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9255020551145864626680617 6941265413359398470010463)
        ·
          refine ⟨10411898120039097705015695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6941265413359398470010463 10411898120039097705015695)
          ·
            refine ⟨15617847180058646557523543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10411898120039097705015695 15617847180058646557523543)
            ·
              refine ⟨23426770770087969836285315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15617847180058646557523543 23426770770087969836285315)
              ·
                refine ⟨35140156155131954754427973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23426770770087969836285315 35140156155131954754427973)
                ·
                  refine ⟨6588779279087241516455245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35140156155131954754427973 6588779279087241516455245)
                  ·
                    refine ⟨2470792229657715568670717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6588779279087241516455245 2470792229657715568670717)
                    ·
                      refine ⟨926547086121643338251519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2470792229657715568670717 926547086121643338251519)
                      ·
                        rfl

theorem cell23_1804444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1804444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804444 prefixEnd_1804444 := by exact prefixLift 1804444
  have htrace : WordTrace (prefixWord ++ tailWord_1804444) baseStart_1804444 baseEnd_1804444 := by
    simpa [prefixWord, tailWord_1804444, baseEnd_1804444] using wordTrace_append hprefix tailTrace_1804444
  have hstable : (prefixWord ++ tailWord_1804444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804444).length < 2 ^ (prefixWord ++ tailWord_1804444).sum := by decide
  have hdescent : baseEnd_1804444 < baseStart_1804444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804445 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_1804445 : Nat := 118140960795 + 1804445 * 2 ^ 59
def prefixEnd_1804445 : Nat := 4983230072969 + 3 ^ 40 * 1804445 * 2
def baseEnd_1804445 : Nat := 926547599602297834339015

theorem tailTrace_1804445 : CollatzResearch.WordTrace tailWord_1804445 prefixEnd_1804445 926547599602297834339015 := by
  unfold tailWord_1804445
  simp only [CollatzResearch.WordTrace]
  refine ⟨65813515947811414516070789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43875677298540943010713859 65813515947811414516070789)
  ·
    refine ⟨12340034240214640221763273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65813515947811414516070789 12340034240214640221763273)
    ·
      refine ⟨9255025680160980166322455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12340034240214640221763273 9255025680160980166322455)
      ·
        refine ⟨13882538520241470249483683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255025680160980166322455 13882538520241470249483683)
        ·
          refine ⟨20823807780362205374225525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13882538520241470249483683 20823807780362205374225525)
          ·
            refine ⟨1952231979408956753833643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20823807780362205374225525 1952231979408956753833643)
            ·
              refine ⟨2928347969113435130750465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952231979408956753833643 2928347969113435130750465)
              ·
                refine ⟨2196260976835076348062849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928347969113435130750465 2196260976835076348062849)
                ·
                  refine ⟨1647195732626307261047137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2196260976835076348062849 1647195732626307261047137)
                  ·
                    refine ⟨1235396799469730445785353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1647195732626307261047137 1235396799469730445785353)
                    ·
                      refine ⟨926547599602297834339015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235396799469730445785353 926547599602297834339015)
                      ·
                        rfl

theorem cell23_1804445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_1804445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804445 prefixEnd_1804445 := by exact prefixLift 1804445
  have htrace : WordTrace (prefixWord ++ tailWord_1804445) baseStart_1804445 baseEnd_1804445 := by
    simpa [prefixWord, tailWord_1804445, baseEnd_1804445] using wordTrace_append hprefix tailTrace_1804445
  have hstable : (prefixWord ++ tailWord_1804445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804445).length < 2 ^ (prefixWord ++ tailWord_1804445).sum := by decide
  have hdescent : baseEnd_1804445 < baseStart_1804445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804461 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1804461 : Nat := 118140960795 + 1804461 * 2 ^ 59
def prefixEnd_1804461 : Nat := 4983230072969 + 3 ^ 40 * 1804461 * 2
def baseEnd_1804461 : Nat := 926555815292769771738941

theorem tailTrace_1804461 : CollatzResearch.WordTrace tailWord_1804461 prefixEnd_1804461 926555815292769771738941 := by
  unfold tailWord_1804461
  simp only [CollatzResearch.WordTrace]
  refine ⟨65814099515753449248653237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43876066343835632832435491 65814099515753449248653237)
  ·
    refine ⟨6170071829601885867061241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65814099515753449248653237 6170071829601885867061241)
    ·
      refine ⟨4627553872201414400295931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6170071829601885867061241 4627553872201414400295931)
      ·
        refine ⟨6941330808302121600443897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627553872201414400295931 6941330808302121600443897)
        ·
          refine ⟨5205998106226591200332923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6941330808302121600443897 5205998106226591200332923)
          ·
            refine ⟨7808997159339886800499385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5205998106226591200332923 7808997159339886800499385)
            ·
              refine ⟨5856747869504915100374539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7808997159339886800499385 5856747869504915100374539)
              ·
                refine ⟨8785121804257372650561809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856747869504915100374539 8785121804257372650561809)
                ·
                  refine ⟨6588841353193029487921357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8785121804257372650561809 6588841353193029487921357)
                  ·
                    refine ⟨2470815507447386057970509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6588841353193029487921357 2470815507447386057970509)
                    ·
                      refine ⟨926555815292769771738941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2470815507447386057970509 926555815292769771738941)
                      ·
                        rfl

theorem cell23_1804461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1804461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804461 prefixEnd_1804461 := by exact prefixLift 1804461
  have htrace : WordTrace (prefixWord ++ tailWord_1804461) baseStart_1804461 baseEnd_1804461 := by
    simpa [prefixWord, tailWord_1804461, baseEnd_1804461] using wordTrace_append hprefix tailTrace_1804461
  have hstable : (prefixWord ++ tailWord_1804461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804461).length < 2 ^ (prefixWord ++ tailWord_1804461).sum := by decide
  have hdescent : baseEnd_1804461 < baseStart_1804461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804462 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1804462 : Nat := 118140960795 + 1804462 * 2 ^ 59
def prefixEnd_1804462 : Nat := 4983230072969 + 3 ^ 40 * 1804462 * 2
def baseEnd_1804462 : Nat := 926556328773424267826437

theorem tailTrace_1804462 : CollatzResearch.WordTrace tailWord_1804462 prefixEnd_1804462 926556328773424267826437 := by
  unfold tailWord_1804462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226766998593728302429955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43876090659166550946293093 8226766998593728302429955)
  ·
    refine ⟨12340150497890592453644933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8226766998593728302429955 12340150497890592453644933)
    ·
      refine ⟨2313778218354486085058425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12340150497890592453644933 2313778218354486085058425)
      ·
        refine ⟨1735333663765864563793819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2313778218354486085058425 1735333663765864563793819)
        ·
          refine ⟨2603000495648796845690729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735333663765864563793819 2603000495648796845690729)
          ·
            refine ⟨1952250371736597634268047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2603000495648796845690729 1952250371736597634268047)
            ·
              refine ⟨2928375557604896451402071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952250371736597634268047 2928375557604896451402071)
              ·
                refine ⟨4392563336407344677103107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928375557604896451402071 4392563336407344677103107)
                ·
                  refine ⟨6588845004611017015654661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392563336407344677103107 6588845004611017015654661)
                  ·
                    refine ⟨1235408438364565690435249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6588845004611017015654661 1235408438364565690435249)
                    ·
                      refine ⟨926556328773424267826437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235408438364565690435249 926556328773424267826437)
                      ·
                        rfl

theorem cell23_1804462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1804462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804462 prefixEnd_1804462 := by exact prefixLift 1804462
  have htrace : WordTrace (prefixWord ++ tailWord_1804462) baseStart_1804462 baseEnd_1804462 := by
    simpa [prefixWord, tailWord_1804462, baseEnd_1804462] using wordTrace_append hprefix tailTrace_1804462
  have hstable : (prefixWord ++ tailWord_1804462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804462).length < 2 ^ (prefixWord ++ tailWord_1804462).sum := by decide
  have hdescent : baseEnd_1804462 < baseStart_1804462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804477 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1804477 : Nat := 118140960795 + 1804477 * 2 ^ 59
def prefixEnd_1804477 : Nat := 4983230072969 + 3 ^ 40 * 1804477 * 2
def baseEnd_1804477 : Nat := 308854676994413903046289

theorem tailTrace_1804477 : CollatzResearch.WordTrace tailWord_1804477 prefixEnd_1804477 308854676994413903046289 := by
  unfold tailWord_1804477
  simp only [CollatzResearch.WordTrace]
  refine ⟨65814683083695483981235685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43876455389130322654157123 65814683083695483981235685)
  ·
    refine ⟨12340253078192903246481691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65814683083695483981235685 12340253078192903246481691)
    ·
      refine ⟨18510379617289354869722537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12340253078192903246481691 18510379617289354869722537)
      ·
        refine ⟨13882784712967016152291903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18510379617289354869722537 13882784712967016152291903)
        ·
          refine ⟨20824177069450524228437855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13882784712967016152291903 20824177069450524228437855)
          ·
            refine ⟨31236265604175786342656783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20824177069450524228437855 31236265604175786342656783)
            ·
              refine ⟨46854398406263679513985175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31236265604175786342656783 46854398406263679513985175)
              ·
                refine ⟨70281597609395519270977763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46854398406263679513985175 70281597609395519270977763)
                ·
                  refine ⟨105422396414093278906466645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70281597609395519270977763 105422396414093278906466645)
                  ·
                    refine ⟨308854676994413903046289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 105422396414093278906466645 308854676994413903046289)
                    ·
                      rfl

theorem cell23_1804477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1804477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804477 prefixEnd_1804477 := by exact prefixLift 1804477
  have htrace : WordTrace (prefixWord ++ tailWord_1804477) baseStart_1804477 baseEnd_1804477 := by
    simpa [prefixWord, tailWord_1804477, baseEnd_1804477] using wordTrace_append hprefix tailTrace_1804477
  have hstable : (prefixWord ++ tailWord_1804477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804477).length < 2 ^ (prefixWord ++ tailWord_1804477).sum := by decide
  have hdescent : baseEnd_1804477 < baseStart_1804477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804487 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1804487 : Nat := 118140960795 + 1804487 * 2 ^ 59
def prefixEnd_1804487 : Nat := 4983230072969 + 3 ^ 40 * 1804487 * 2
def baseEnd_1804487 : Nat := 926569165789786670013821

theorem tailTrace_1804487 : CollatzResearch.WordTrace tailWord_1804487 prefixEnd_1804487 926569165789786670013821 := by
  unfold tailWord_1804487
  simp only [CollatzResearch.WordTrace]
  refine ⟨65815047813659255689099715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43876698542439503792733143 65815047813659255689099715)
  ·
    refine ⟨98722571720488883533649573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65815047813659255689099715 98722571720488883533649573)
    ·
      refine ⟨18510482197591665662559295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98722571720488883533649573 18510482197591665662559295)
      ·
        refine ⟨27765723296387498493838943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18510482197591665662559295 27765723296387498493838943)
        ·
          refine ⟨41648584944581247740758415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27765723296387498493838943 41648584944581247740758415)
          ·
            refine ⟨62472877416871871611137623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41648584944581247740758415 62472877416871871611137623)
            ·
              refine ⟨93709316125307807416706435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62472877416871871611137623 93709316125307807416706435)
              ·
                refine ⟨140563974187961711125059653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93709316125307807416706435 140563974187961711125059653)
                ·
                  refine ⟨26355745160242820835948685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140563974187961711125059653 26355745160242820835948685)
                  ·
                    refine ⟨9883404435091057813480757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26355745160242820835948685 9883404435091057813480757)
                    ·
                      refine ⟨926569165789786670013821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9883404435091057813480757 926569165789786670013821)
                      ·
                        rfl

theorem cell23_1804487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1804487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804487 prefixEnd_1804487 := by exact prefixLift 1804487
  have htrace : WordTrace (prefixWord ++ tailWord_1804487) baseStart_1804487 baseEnd_1804487 := by
    simpa [prefixWord, tailWord_1804487, baseEnd_1804487] using wordTrace_append hprefix tailTrace_1804487
  have hstable : (prefixWord ++ tailWord_1804487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804487).length < 2 ^ (prefixWord ++ tailWord_1804487).sum := by decide
  have hdescent : baseEnd_1804487 < baseStart_1804487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804497 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_1804497 : Nat := 118140960795 + 1804497 * 2 ^ 59
def prefixEnd_1804497 : Nat := 4983230072969 + 3 ^ 40 * 1804497 * 2
def baseEnd_1804497 : Nat := 926574300596331630888775

theorem tailTrace_1804497 : CollatzResearch.WordTrace tailWord_1804497 prefixEnd_1804497 926574300596331630888775 := by
  unfold tailWord_1804497
  simp only [CollatzResearch.WordTrace]
  refine ⟨65815412543623027396963745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43876941695748684931309163 65815412543623027396963745)
  ·
    refine ⟨49361559407717270547722809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65815412543623027396963745 49361559407717270547722809)
    ·
      refine ⟨37021169555787952910792107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49361559407717270547722809 37021169555787952910792107)
      ·
        refine ⟨55531754333681929366188161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37021169555787952910792107 55531754333681929366188161)
        ·
          refine ⟨41648815750261447024641121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55531754333681929366188161 41648815750261447024641121)
          ·
            refine ⟨31236611812696085268480841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41648815750261447024641121 31236611812696085268480841)
            ·
              refine ⟨23427458859522063951360631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31236611812696085268480841 23427458859522063951360631)
              ·
                refine ⟨35141188289283095927040947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23427458859522063951360631 35141188289283095927040947)
                ·
                  refine ⟨52711782433924643890561421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35141188289283095927040947 52711782433924643890561421)
                  ·
                    refine ⟨19766918412721741458960533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52711782433924643890561421 19766918412721741458960533)
                    ·
                      refine ⟨926574300596331630888775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19766918412721741458960533 926574300596331630888775)
                      ·
                        rfl

theorem cell23_1804497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_1804497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804497 prefixEnd_1804497 := by exact prefixLift 1804497
  have htrace : WordTrace (prefixWord ++ tailWord_1804497) baseStart_1804497 baseEnd_1804497 := by
    simpa [prefixWord, tailWord_1804497, baseEnd_1804497] using wordTrace_append hprefix tailTrace_1804497
  have hstable : (prefixWord ++ tailWord_1804497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804497).length < 2 ^ (prefixWord ++ tailWord_1804497).sum := by decide
  have hdescent : baseEnd_1804497 < baseStart_1804497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804508 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1804508 : Nat := 118140960795 + 1804508 * 2 ^ 59
def prefixEnd_1804508 : Nat := 4983230072969 + 3 ^ 40 * 1804508 * 2
def baseEnd_1804508 : Nat := 926579948883531087851225

theorem tailTrace_1804508 : CollatzResearch.WordTrace tailWord_1804508 prefixEnd_1804508 926579948883531087851225 := by
  unfold tailWord_1804508
  simp only [CollatzResearch.WordTrace]
  refine ⟨32907906873291588137807089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43877209164388784183742785 32907906873291588137807089)
  ·
    refine ⟨24680930154968691103355317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32907906873291588137807089 24680930154968691103355317)
    ·
      refine ⟨2313837202028314790939561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24680930154968691103355317 2313837202028314790939561)
      ·
        refine ⟨1735377901521236093204671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2313837202028314790939561 1735377901521236093204671)
        ·
          refine ⟨2603066852281854139807007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735377901521236093204671 2603066852281854139807007)
          ·
            refine ⟨3904600278422781209710511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603066852281854139807007 3904600278422781209710511)
            ·
              refine ⟨5856900417634171814565767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904600278422781209710511 5856900417634171814565767)
              ·
                refine ⟨8785350626451257721848651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856900417634171814565767 8785350626451257721848651)
                ·
                  refine ⟨13178025939676886582772977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8785350626451257721848651 13178025939676886582772977)
                  ·
                    refine ⟨9883519454757664937079733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13178025939676886582772977 9883519454757664937079733)
                    ·
                      refine ⟨926579948883531087851225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9883519454757664937079733 926579948883531087851225)
                      ·
                        rfl

theorem cell23_1804508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1804508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804508 prefixEnd_1804508 := by exact prefixLift 1804508
  have htrace : WordTrace (prefixWord ++ tailWord_1804508) baseStart_1804508 baseEnd_1804508 := by
    simpa [prefixWord, tailWord_1804508, baseEnd_1804508] using wordTrace_append hprefix tailTrace_1804508
  have hstable : (prefixWord ++ tailWord_1804508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804508).length < 2 ^ (prefixWord ++ tailWord_1804508).sum := by decide
  have hdescent : baseEnd_1804508 < baseStart_1804508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804524 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 6]
def baseStart_1804524 : Nat := 118140960795 + 1804524 * 2 ^ 59
def prefixEnd_1804524 : Nat := 4983230072969 + 3 ^ 40 * 1804524 * 2
def baseEnd_1804524 : Nat := 102954240508222558361239

theorem tailTrace_1804524 : CollatzResearch.WordTrace tailWord_1804524 prefixEnd_1804524 102954240508222558361239 := by
  unfold tailWord_1804524
  simp only [CollatzResearch.WordTrace]
  refine ⟨32908198657262605504098313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43877598209683474005464417 32908198657262605504098313)
  ·
    refine ⟨24681148992946954128073735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32908198657262605504098313 24681148992946954128073735)
    ·
      refine ⟨37021723489420431192110603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24681148992946954128073735 37021723489420431192110603)
      ·
        refine ⟨55532585234130646788165905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37021723489420431192110603 55532585234130646788165905)
        ·
          refine ⟨41649438925597985091124429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55532585234130646788165905 41649438925597985091124429)
          ·
            refine ⟨15618539597099244409171661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41649438925597985091124429 15618539597099244409171661)
            ·
              refine ⟨5856952348912216653439373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15618539597099244409171661 5856952348912216653439373)
              ·
                refine ⟨2196357130842081245039765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5856952348912216653439373 2196357130842081245039765)
                ·
                  refine ⟨102954240508222558361239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2196357130842081245039765 102954240508222558361239)
                  ·
                    rfl

theorem cell23_1804524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_1804524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804524 prefixEnd_1804524 := by exact prefixLift 1804524
  have htrace : WordTrace (prefixWord ++ tailWord_1804524) baseStart_1804524 baseEnd_1804524 := by
    simpa [prefixWord, tailWord_1804524, baseEnd_1804524] using wordTrace_append hprefix tailTrace_1804524
  have hstable : (prefixWord ++ tailWord_1804524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804524).length < 2 ^ (prefixWord ++ tailWord_1804524).sum := by decide
  have hdescent : baseEnd_1804524 < baseStart_1804524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804601 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 1, 6]
def baseStart_1804601 : Nat := 118140960795 + 1804601 * 2 ^ 59
def prefixEnd_1804601 : Nat := 4983230072969 + 3 ^ 40 * 1804601 * 2
def baseEnd_1804601 : Nat := 308875900861466407996099

theorem tailTrace_1804601 : CollatzResearch.WordTrace tailWord_1804601 prefixEnd_1804601 308875900861466407996099 := by
  unfold tailWord_1804601
  simp only [CollatzResearch.WordTrace]
  refine ⟨65819205735246253158749657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43879470490164168772499771 65819205735246253158749657)
  ·
    refine ⟨49364404301434689869062243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65819205735246253158749657 49364404301434689869062243)
    ·
      refine ⟨74046606452152034803593365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49364404301434689869062243 74046606452152034803593365)
      ·
        refine ⟨3470934677444626631418439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74046606452152034803593365 3470934677444626631418439)
        ·
          refine ⟨5206402016166939947127659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470934677444626631418439 5206402016166939947127659)
          ·
            refine ⟨7809603024250409920691489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206402016166939947127659 7809603024250409920691489)
            ·
              refine ⟨5857202268187807440518617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7809603024250409920691489 5857202268187807440518617)
              ·
                refine ⟨4392901701140855580388963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5857202268187807440518617 4392901701140855580388963)
                ·
                  refine ⟨6589352551711283370583445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392901701140855580388963 6589352551711283370583445)
                  ·
                    refine ⟨308875900861466407996099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6589352551711283370583445 308875900861466407996099)
                    ·
                      rfl

theorem cell23_1804601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_1804601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804601 prefixEnd_1804601 := by exact prefixLift 1804601
  have htrace : WordTrace (prefixWord ++ tailWord_1804601) baseStart_1804601 baseEnd_1804601 := by
    simpa [prefixWord, tailWord_1804601, baseEnd_1804601] using wordTrace_append hprefix tailTrace_1804601
  have hstable : (prefixWord ++ tailWord_1804601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804601).length < 2 ^ (prefixWord ++ tailWord_1804601).sum := by decide
  have hdescent : baseEnd_1804601 < baseStart_1804601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804625 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 3, 2, 2]
def baseStart_1804625 : Nat := 118140960795 + 1804625 * 2 ^ 59
def prefixEnd_1804625 : Nat := 4983230072969 + 3 ^ 40 * 1804625 * 2
def baseEnd_1804625 : Nat := 926640026120107130088187

theorem tailTrace_1804625 : CollatzResearch.WordTrace tailWord_1804625 prefixEnd_1804625 926640026120107130088187 := by
  unfold tailWord_1804625
  simp only [CollatzResearch.WordTrace]
  refine ⟨65820081087159305257623329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43880054058106203505082219 65820081087159305257623329)
  ·
    refine ⟨49365060815369478943217497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65820081087159305257623329 49365060815369478943217497)
    ·
      refine ⟨37023795611527109207413123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49365060815369478943217497 37023795611527109207413123)
      ·
        refine ⟨55535693417290663811119685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37023795611527109207413123 55535693417290663811119685)
        ·
          refine ⟨10412942515741999464584941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55535693417290663811119685 10412942515741999464584941)
          ·
            refine ⟨3904853443403249799219353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10412942515741999464584941 3904853443403249799219353)
            ·
              refine ⟨2928640082552437349414515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3904853443403249799219353 2928640082552437349414515)
              ·
                refine ⟨4392960123828656024121773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928640082552437349414515 4392960123828656024121773)
                ·
                  refine ⟨1647360046435746009045665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4392960123828656024121773 1647360046435746009045665)
                  ·
                    refine ⟨1235520034826809506784249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1647360046435746009045665 1235520034826809506784249)
                    ·
                      refine ⟨926640026120107130088187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235520034826809506784249 926640026120107130088187)
                      ·
                        rfl

theorem cell23_1804625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_1804625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804625 prefixEnd_1804625 := by exact prefixLift 1804625
  have htrace : WordTrace (prefixWord ++ tailWord_1804625) baseStart_1804625 baseEnd_1804625 := by
    simpa [prefixWord, tailWord_1804625, baseEnd_1804625] using wordTrace_append hprefix tailTrace_1804625
  have hstable : (prefixWord ++ tailWord_1804625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804625).length < 2 ^ (prefixWord ++ tailWord_1804625).sum := by decide
  have hdescent : baseEnd_1804625 < baseStart_1804625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804648 : List Nat := [2, 1, 4, 2, 2, 3, 2, 7]
def baseStart_1804648 : Nat := 118140960795 + 1804648 * 2 ^ 59
def prefixEnd_1804648 : Nat := 4983230072969 + 3 ^ 40 * 1804648 * 2
def baseEnd_1804648 : Nat := 34320438376857797781503

theorem tailTrace_1804648 : CollatzResearch.WordTrace tailWord_1804648 prefixEnd_1804648 34320438376857797781503 := by
  unfold tailWord_1804648
  simp only [CollatzResearch.WordTrace]
  refine ⟨32910459983037990092855299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43880613310717320123807065 32910459983037990092855299)
  ·
    refine ⟨49365689974556985139282949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32910459983037990092855299 49365689974556985139282949)
    ·
      refine ⟨9256066870229434713615553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49365689974556985139282949 9256066870229434713615553)
      ·
        refine ⟨6942050152672076035211665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9256066870229434713615553 6942050152672076035211665)
        ·
          refine ⟨5206537614504057026408749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6942050152672076035211665 5206537614504057026408749)
          ·
            refine ⟨1952451605439021384903281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5206537614504057026408749 1952451605439021384903281)
            ·
              refine ⟨1464338704079266038677461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1952451605439021384903281 1464338704079266038677461)
              ·
                refine ⟨34320438376857797781503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1464338704079266038677461 34320438376857797781503)
                ·
                  rfl

theorem cell23_1804648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 7].length) (baseStart_1804648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804648 prefixEnd_1804648 := by exact prefixLift 1804648
  have htrace : WordTrace (prefixWord ++ tailWord_1804648) baseStart_1804648 baseEnd_1804648 := by
    simpa [prefixWord, tailWord_1804648, baseEnd_1804648] using wordTrace_append hprefix tailTrace_1804648
  have hstable : (prefixWord ++ tailWord_1804648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804648).length < 2 ^ (prefixWord ++ tailWord_1804648).sum := by decide
  have hdescent : baseEnd_1804648 < baseStart_1804648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804658 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_1804658 : Nat := 118140960795 + 1804658 * 2 ^ 59
def prefixEnd_1804658 : Nat := 4983230072969 + 3 ^ 40 * 1804658 * 2
def baseEnd_1804658 : Nat := 926656970981705500975535

theorem tailTrace_1804658 : CollatzResearch.WordTrace tailWord_1804658 prefixEnd_1804658 926656970981705500975535 := by
  unfold tailWord_1804658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16455321174009937973393657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43880856464026501262383085 16455321174009937973393657)
  ·
    refine ⟨12341490880507453480045243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16455321174009937973393657 12341490880507453480045243)
    ·
      refine ⟨18512236320761180220067865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12341490880507453480045243 18512236320761180220067865)
      ·
        refine ⟨13884177240570885165050899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18512236320761180220067865 13884177240570885165050899)
        ·
          refine ⟨20826265860856327747576349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13884177240570885165050899 20826265860856327747576349)
          ·
            refine ⟨7809849697821122905341131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20826265860856327747576349 7809849697821122905341131)
            ·
              refine ⟨11714774546731684358011697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7809849697821122905341131 11714774546731684358011697)
              ·
                refine ⟨8786080910048763268508773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11714774546731684358011697 8786080910048763268508773)
                ·
                  refine ⟨1647390170634143112845395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8786080910048763268508773 1647390170634143112845395)
                  ·
                    refine ⟨2471085255951214669268093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1647390170634143112845395 2471085255951214669268093)
                    ·
                      refine ⟨926656970981705500975535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2471085255951214669268093 926656970981705500975535)
                      ·
                        rfl

theorem cell23_1804658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_1804658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804658 prefixEnd_1804658 := by exact prefixLift 1804658
  have htrace : WordTrace (prefixWord ++ tailWord_1804658) baseStart_1804658 baseEnd_1804658 := by
    simpa [prefixWord, tailWord_1804658, baseEnd_1804658] using wordTrace_append hprefix tailTrace_1804658
  have hstable : (prefixWord ++ tailWord_1804658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804658).length < 2 ^ (prefixWord ++ tailWord_1804658).sum := by decide
  have hdescent : baseEnd_1804658 < baseStart_1804658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804692 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1804692 : Nat := 118140960795 + 1804692 * 2 ^ 59
def prefixEnd_1804692 : Nat := 4983230072969 + 3 ^ 40 * 1804692 * 2
def baseEnd_1804692 : Nat := 926674429323958367950379

theorem tailTrace_1804692 : CollatzResearch.WordTrace tailWord_1804692 prefixEnd_1804692 926674429323958367950379 := by
  unfold tailWord_1804692
  simp only [CollatzResearch.WordTrace]
  refine ⟨32911262388958287850156165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43881683185277717133541553 32911262388958287850156165)
  ·
    refine ⟨6170861697929678971904281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32911262388958287850156165 6170861697929678971904281)
    ·
      refine ⟨4628146273447259228928211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6170861697929678971904281 4628146273447259228928211)
      ·
        refine ⟨6942219410170888843392317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628146273447259228928211 6942219410170888843392317)
        ·
          refine ⟨2603332278814083316272119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6942219410170888843392317 2603332278814083316272119)
          ·
            refine ⟨3904998418221124974408179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603332278814083316272119 3904998418221124974408179)
            ·
              refine ⟨5857497627331687461612269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904998418221124974408179 5857497627331687461612269)
              ·
                refine ⟨2196561610249382798104601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5857497627331687461612269 2196561610249382798104601)
                ·
                  refine ⟨1647421207687037098578451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2196561610249382798104601 1647421207687037098578451)
                  ·
                    refine ⟨2471131811530555647867677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1647421207687037098578451 2471131811530555647867677)
                    ·
                      refine ⟨926674429323958367950379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2471131811530555647867677 926674429323958367950379)
                      ·
                        rfl

theorem cell23_1804692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1804692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804692 prefixEnd_1804692 := by exact prefixLift 1804692
  have htrace : WordTrace (prefixWord ++ tailWord_1804692) baseStart_1804692 baseEnd_1804692 := by
    simpa [prefixWord, tailWord_1804692, baseEnd_1804692] using wordTrace_append hprefix tailTrace_1804692
  have hstable : (prefixWord ++ tailWord_1804692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804692).length < 2 ^ (prefixWord ++ tailWord_1804692).sum := by decide
  have hdescent : baseEnd_1804692 < baseStart_1804692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804702 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1804702 : Nat := 118140960795 + 1804702 * 2 ^ 59
def prefixEnd_1804702 : Nat := 4983230072969 + 3 ^ 40 * 1804702 * 2
def baseEnd_1804702 : Nat := 926679564130503328825333

theorem tailTrace_1804702 : CollatzResearch.WordTrace tailWord_1804702 prefixEnd_1804702 926679564130503328825333 := by
  unfold tailWord_1804702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8227861188485043426022045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43881926338586898272117573 8227861188485043426022045)
  ·
    refine ⟨3085447945681891284758267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8227861188485043426022045 3085447945681891284758267)
    ·
      refine ⟨4628171918522836927137401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3085447945681891284758267 4628171918522836927137401)
      ·
        refine ⟨3471128938892127695353051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4628171918522836927137401 3471128938892127695353051)
        ·
          refine ⟨5206693408338191543029577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471128938892127695353051 5206693408338191543029577)
          ·
            refine ⟨3905020056253643657272183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5206693408338191543029577 3905020056253643657272183)
            ·
              refine ⟨5857530084380465485908275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3905020056253643657272183 5857530084380465485908275)
              ·
                refine ⟨8786295126570698228862413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857530084380465485908275 8786295126570698228862413)
                ·
                  refine ⟨3294860672464011835823405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8786295126570698228862413 3294860672464011835823405)
                  ·
                    refine ⟨1235572752174004438433777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294860672464011835823405 1235572752174004438433777)
                    ·
                      refine ⟨926679564130503328825333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235572752174004438433777 926679564130503328825333)
                      ·
                        rfl

theorem cell23_1804702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1804702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804702 prefixEnd_1804702 := by exact prefixLift 1804702
  have htrace : WordTrace (prefixWord ++ tailWord_1804702) baseStart_1804702 baseEnd_1804702 := by
    simpa [prefixWord, tailWord_1804702, baseEnd_1804702] using wordTrace_append hprefix tailTrace_1804702
  have hstable : (prefixWord ++ tailWord_1804702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804702).length < 2 ^ (prefixWord ++ tailWord_1804702).sum := by decide
  have hdescent : baseEnd_1804702 < baseStart_1804702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804732 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1804732 : Nat := 118140960795 + 1804732 * 2 ^ 59
def prefixEnd_1804732 : Nat := 4983230072969 + 3 ^ 40 * 1804732 * 2
def baseEnd_1804732 : Nat := 926694968550138211450195

theorem tailTrace_1804732 : CollatzResearch.WordTrace tailWord_1804732 prefixEnd_1804732 926694968550138211450195 := by
  unfold tailWord_1804732
  simp only [CollatzResearch.WordTrace]
  refine ⟨32911991848885831265884225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43882655798514441687845633 32911991848885831265884225)
  ·
    refine ⟨24683993886664373449413169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32911991848885831265884225 24683993886664373449413169)
    ·
      refine ⟨18512995414998280087059877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24683993886664373449413169 18512995414998280087059877)
      ·
        refine ⟨3471186640312177516323727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18512995414998280087059877 3471186640312177516323727)
        ·
          refine ⟨5206779960468266274485591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471186640312177516323727 5206779960468266274485591)
          ·
            refine ⟨7810169940702399411728387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206779960468266274485591 7810169940702399411728387)
            ·
              refine ⟨11715254911053599117592581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810169940702399411728387 11715254911053599117592581)
              ·
                refine ⟨2196610295822549834548609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11715254911053599117592581 2196610295822549834548609)
                ·
                  refine ⟨1647457721866912375911457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2196610295822549834548609 1647457721866912375911457)
                  ·
                    refine ⟨1235593291400184281933593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1647457721866912375911457 1235593291400184281933593)
                    ·
                      refine ⟨926694968550138211450195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235593291400184281933593 926694968550138211450195)
                      ·
                        rfl

theorem cell23_1804732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1804732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804732 prefixEnd_1804732 := by exact prefixLift 1804732
  have htrace : WordTrace (prefixWord ++ tailWord_1804732) baseStart_1804732 baseEnd_1804732 := by
    simpa [prefixWord, tailWord_1804732, baseEnd_1804732] using wordTrace_append hprefix tailTrace_1804732
  have hstable : (prefixWord ++ tailWord_1804732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804732).length < 2 ^ (prefixWord ++ tailWord_1804732).sum := by decide
  have hdescent : baseEnd_1804732 < baseStart_1804732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804862 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_1804862 : Nat := 118140960795 + 1804862 * 2 ^ 59
def prefixEnd_1804862 : Nat := 4983230072969 + 3 ^ 40 * 1804862 * 2
def baseEnd_1804862 : Nat := 102973524559469189202733

theorem tailTrace_1804862 : CollatzResearch.WordTrace tailWord_1804862 prefixEnd_1804862 102973524559469189202733 := by
  unfold tailWord_1804862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8228590648412586841750105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43885816791533796489333893 8228590648412586841750105)
  ·
    refine ⟨6171442986309440131312579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8228590648412586841750105 6171442986309440131312579)
    ·
      refine ⟨9257164479464160196968869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6171442986309440131312579 9257164479464160196968869)
      ·
        refine ⟨1735718339899530036931663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9257164479464160196968869 1735718339899530036931663)
        ·
          refine ⟨2603577509849295055397495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735718339899530036931663 2603577509849295055397495)
          ·
            refine ⟨3905366264773942583096243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603577509849295055397495 3905366264773942583096243)
            ·
              refine ⟨5858049397160913874644365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3905366264773942583096243 5858049397160913874644365)
              ·
                refine ⟨2196768523935342702991637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5858049397160913874644365 2196768523935342702991637)
                ·
                  refine ⟨102973524559469189202733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2196768523935342702991637 102973524559469189202733)
                  ·
                    rfl

theorem cell23_1804862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_1804862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804862 prefixEnd_1804862 := by exact prefixLift 1804862
  have htrace : WordTrace (prefixWord ++ tailWord_1804862) baseStart_1804862 baseEnd_1804862 := by
    simpa [prefixWord, tailWord_1804862, baseEnd_1804862] using wordTrace_append hprefix tailTrace_1804862
  have hstable : (prefixWord ++ tailWord_1804862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804862).length < 2 ^ (prefixWord ++ tailWord_1804862).sum := by decide
  have hdescent : baseEnd_1804862 < baseStart_1804862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804882 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_1804882 : Nat := 118140960795 + 1804882 * 2 ^ 59
def prefixEnd_1804882 : Nat := 4983230072969 + 3 ^ 40 * 1804882 * 2
def baseEnd_1804882 : Nat := 926771990648312624574505

theorem tailTrace_1804882 : CollatzResearch.WordTrace tailWord_1804882 prefixEnd_1804882 926771990648312624574505 := by
  unfold tailWord_1804882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16457363661807059537432225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43886303098152158766485933 16457363661807059537432225)
  ·
    refine ⟨12343022746355294653074169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16457363661807059537432225 12343022746355294653074169)
    ·
      refine ⟨9257267059766470989805627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12343022746355294653074169 9257267059766470989805627)
      ·
        refine ⟨13885900589649706484708441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9257267059766470989805627 13885900589649706484708441)
        ·
          refine ⟨10414425442237279863531331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13885900589649706484708441 10414425442237279863531331)
          ·
            refine ⟨15621638163355919795296997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10414425442237279863531331 15621638163355919795296997)
            ·
              refine ⟨2929057155629234961618187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15621638163355919795296997 2929057155629234961618187)
              ·
                refine ⟨4393585733443852442427281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929057155629234961618187 4393585733443852442427281)
                ·
                  refine ⟨3295189300082889331820461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4393585733443852442427281 3295189300082889331820461)
                  ·
                    refine ⟨1235695987531083499432673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295189300082889331820461 1235695987531083499432673)
                    ·
                      refine ⟨926771990648312624574505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235695987531083499432673 926771990648312624574505)
                      ·
                        rfl

theorem cell23_1804882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_1804882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804882 prefixEnd_1804882 := by exact prefixLift 1804882
  have htrace : WordTrace (prefixWord ++ tailWord_1804882) baseStart_1804882 baseEnd_1804882 := by
    simpa [prefixWord, tailWord_1804882, baseEnd_1804882] using wordTrace_append hprefix tailTrace_1804882
  have hstable : (prefixWord ++ tailWord_1804882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804882).length < 2 ^ (prefixWord ++ tailWord_1804882).sum := by decide
  have hdescent : baseEnd_1804882 < baseStart_1804882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804888 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 6, 4]
def baseStart_1804888 : Nat := 118140960795 + 1804888 * 2 ^ 59
def prefixEnd_1804888 : Nat := 4983230072969 + 3 ^ 40 * 1804888 * 2
def baseEnd_1804888 : Nat := 308925023844079867033159

theorem tailTrace_1804888 : CollatzResearch.WordTrace tailWord_1804888 prefixEnd_1804888 308925023844079867033159 := by
  unfold tailWord_1804888
  simp only [CollatzResearch.WordTrace]
  refine ⟨32914836742603250587223659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43886448990137667449631545 32914836742603250587223659)
  ·
    refine ⟨49372255113904875880835489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32914836742603250587223659 49372255113904875880835489)
    ·
      refine ⟨37029191335428656910626617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49372255113904875880835489 37029191335428656910626617)
      ·
        refine ⟨27771893501571492682969963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37029191335428656910626617 27771893501571492682969963)
        ·
          refine ⟨41657840252357239024454945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27771893501571492682969963 41657840252357239024454945)
          ·
            refine ⟨31243380189267929268341209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41657840252357239024454945 31243380189267929268341209)
            ·
              refine ⟨23432535141950946951255907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31243380189267929268341209 23432535141950946951255907)
              ·
                refine ⟨35148802712926420426883861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23432535141950946951255907 35148802712926420426883861)
                ·
                  refine ⟨1647600127168425957510181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35148802712926420426883861 1647600127168425957510181)
                  ·
                    refine ⟨308925023844079867033159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1647600127168425957510181 308925023844079867033159)
                    ·
                      rfl

theorem cell23_1804888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_1804888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804888 prefixEnd_1804888 := by exact prefixLift 1804888
  have htrace : WordTrace (prefixWord ++ tailWord_1804888) baseStart_1804888 baseEnd_1804888 := by
    simpa [prefixWord, tailWord_1804888, baseEnd_1804888] using wordTrace_append hprefix tailTrace_1804888
  have hstable : (prefixWord ++ tailWord_1804888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804888).length < 2 ^ (prefixWord ++ tailWord_1804888).sum := by decide
  have hdescent : baseEnd_1804888 < baseStart_1804888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804901 : List Nat := [1, 3, 1, 3, 15]
def baseStart_1804901 : Nat := 118140960795 + 1804901 * 2 ^ 59
def prefixEnd_1804901 : Nat := 4983230072969 + 3 ^ 40 * 1804901 * 2
def baseEnd_1804901 : Nat := 1271305551139572085373

theorem tailTrace_1804901 : CollatzResearch.WordTrace tailWord_1804901 prefixEnd_1804901 1271305551139572085373 := by
  unfold tailWord_1804901
  simp only [CollatzResearch.WordTrace]
  refine ⟨65830147634159404394670557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43886765089439602929780371 65830147634159404394670557)
  ·
    refine ⟨24686305362809776648001459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65830147634159404394670557 24686305362809776648001459)
    ·
      refine ⟨37029458044214664972002189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24686305362809776648001459 37029458044214664972002189)
      ·
        refine ⟨13886046766580499364500821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37029458044214664972002189 13886046766580499364500821)
        ·
          refine ⟨1271305551139572085373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 13886046766580499364500821 1271305551139572085373)
          ·
            rfl

theorem cell23_1804901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 15].length) (baseStart_1804901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804901 prefixEnd_1804901 := by exact prefixLift 1804901
  have htrace : WordTrace (prefixWord ++ tailWord_1804901) baseStart_1804901 baseEnd_1804901 := by
    simpa [prefixWord, tailWord_1804901, baseEnd_1804901] using wordTrace_append hprefix tailTrace_1804901
  have hstable : (prefixWord ++ tailWord_1804901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804901).length < 2 ^ (prefixWord ++ tailWord_1804901).sum := by decide
  have hdescent : baseEnd_1804901 < baseStart_1804901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804946 : List Nat := [3, 2, 3, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_1804946 : Nat := 118140960795 + 1804946 * 2 ^ 59
def prefixEnd_1804946 : Nat := 4983230072969 + 3 ^ 40 * 1804946 * 2
def baseEnd_1804946 : Nat := 926804853410200374174211

theorem tailTrace_1804946 : CollatzResearch.WordTrace tailWord_1804946 prefixEnd_1804946 926804853410200374174211 := by
  unfold tailWord_1804946
  simp only [CollatzResearch.WordTrace]
  refine ⟨16457947229749094270014673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43887859279330918053372461 16457947229749094270014673)
  ·
    refine ⟨12343460422311820702511005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16457947229749094270014673 12343460422311820702511005)
    ·
      refine ⟨4628797658366932763441627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12343460422311820702511005 4628797658366932763441627)
      ·
        refine ⟨6943196487550399145162441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628797658366932763441627 6943196487550399145162441)
        ·
          refine ⟨5207397365662799358871831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6943196487550399145162441 5207397365662799358871831)
          ·
            refine ⟨7811096048494199038307747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207397365662799358871831 7811096048494199038307747)
            ·
              refine ⟨11716644072741298557461621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7811096048494199038307747 11716644072741298557461621)
              ·
                refine ⟨1098435381819496739762027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11716644072741298557461621 1098435381819496739762027)
                ·
                  refine ⟨1647653072729245109643041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098435381819496739762027 1647653072729245109643041)
                  ·
                    refine ⟨1235739804546933832232281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1647653072729245109643041 1235739804546933832232281)
                    ·
                      refine ⟨926804853410200374174211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235739804546933832232281 926804853410200374174211)
                      ·
                        rfl

theorem cell23_1804946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_1804946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804946 prefixEnd_1804946 := by exact prefixLift 1804946
  have htrace : WordTrace (prefixWord ++ tailWord_1804946) baseStart_1804946 baseEnd_1804946 := by
    simpa [prefixWord, tailWord_1804946, baseEnd_1804946] using wordTrace_append hprefix tailTrace_1804946
  have hstable : (prefixWord ++ tailWord_1804946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804946).length < 2 ^ (prefixWord ++ tailWord_1804946).sum := by decide
  have hdescent : baseEnd_1804946 < baseStart_1804946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804979 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 2, 1, 3]
def baseStart_1804979 : Nat := 118140960795 + 1804979 * 2 ^ 59
def prefixEnd_1804979 : Nat := 4983230072969 + 3 ^ 40 * 1804979 * 2
def baseEnd_1804979 : Nat := 926821798271798745061559

theorem tailTrace_1804979 : CollatzResearch.WordTrace tailWord_1804979 prefixEnd_1804979 926821798271798745061559 := by
  unfold tailWord_1804979
  simp only [CollatzResearch.WordTrace]
  refine ⟨65832992527876823716009991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43888661685251215810673327 65832992527876823716009991)
  ·
    refine ⟨98749488791815235574014987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65832992527876823716009991 98749488791815235574014987)
    ·
      refine ⟨148124233187722853361022481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98749488791815235574014987 148124233187722853361022481)
      ·
        refine ⟨111093174890792140020766861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148124233187722853361022481 111093174890792140020766861)
        ·
          refine ⟨41659940584047052507787573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111093174890792140020766861 41659940584047052507787573)
          ·
            refine ⟨3905619429754411172605085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41659940584047052507787573 3905619429754411172605085)
            ·
              refine ⟨1464607286157904189726907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3905619429754411172605085 1464607286157904189726907)
              ·
                refine ⟨2196910929236856284590361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464607286157904189726907 2196910929236856284590361)
                ·
                  refine ⟨1647683196927642213442771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2196910929236856284590361 1647683196927642213442771)
                  ·
                    refine ⟨2471524795391463320164157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1647683196927642213442771 2471524795391463320164157)
                    ·
                      refine ⟨926821798271798745061559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2471524795391463320164157 926821798271798745061559)
                      ·
                        rfl

theorem cell23_1804979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 1, 3].length) (baseStart_1804979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804979 prefixEnd_1804979 := by exact prefixLift 1804979
  have htrace : WordTrace (prefixWord ++ tailWord_1804979) baseStart_1804979 baseEnd_1804979 := by
    simpa [prefixWord, tailWord_1804979, baseEnd_1804979] using wordTrace_append hprefix tailTrace_1804979
  have hstable : (prefixWord ++ tailWord_1804979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804979).length < 2 ^ (prefixWord ++ tailWord_1804979).sum := by decide
  have hdescent : baseEnd_1804979 < baseStart_1804979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804989 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_1804989 : Nat := 118140960795 + 1804989 * 2 ^ 59
def prefixEnd_1804989 : Nat := 4983230072969 + 3 ^ 40 * 1804989 * 2
def baseEnd_1804989 : Nat := 926826933078343705936513

theorem tailTrace_1804989 : CollatzResearch.WordTrace tailWord_1804989 prefixEnd_1804989 926826933078343705936513 := by
  unfold tailWord_1804989
  simp only [CollatzResearch.WordTrace]
  refine ⟨65833357257840595423874021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43888904838560396949249347 65833357257840595423874021)
  ·
    refine ⟨12343754485845111641976379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65833357257840595423874021 12343754485845111641976379)
    ·
      refine ⟨18515631728767667462964569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12343754485845111641976379 18515631728767667462964569)
      ·
        refine ⟨13886723796575750597223427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18515631728767667462964569 13886723796575750597223427)
        ·
          refine ⟨20830085694863625895835141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13886723796575750597223427 20830085694863625895835141)
          ·
            refine ⟨3905641067786929855469089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20830085694863625895835141 3905641067786929855469089)
            ·
              refine ⟨2929230800840197391601817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3905641067786929855469089 2929230800840197391601817)
              ·
                refine ⟨2196923100630148043701363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2929230800840197391601817 2196923100630148043701363)
                ·
                  refine ⟨3295384650945222065552045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196923100630148043701363 3295384650945222065552045)
                  ·
                    refine ⟨1235769244104458274582017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295384650945222065552045 1235769244104458274582017)
                    ·
                      refine ⟨926826933078343705936513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235769244104458274582017 926826933078343705936513)
                      ·
                        rfl

theorem cell23_1804989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_1804989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1804989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1804989 prefixEnd_1804989 := by exact prefixLift 1804989
  have htrace : WordTrace (prefixWord ++ tailWord_1804989) baseStart_1804989 baseEnd_1804989 := by
    simpa [prefixWord, tailWord_1804989, baseEnd_1804989] using wordTrace_append hprefix tailTrace_1804989
  have hstable : (prefixWord ++ tailWord_1804989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804989).length < 2 ^ (prefixWord ++ tailWord_1804989).sum := by decide
  have hdescent : baseEnd_1804989 < baseStart_1804989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805018 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1805018 : Nat := 118140960795 + 1805018 * 2 ^ 59
def prefixEnd_1805018 : Nat := 4983230072969 + 3 ^ 40 * 1805018 * 2
def baseEnd_1805018 : Nat := 926841824017324092473879

theorem tailTrace_1805018 : CollatzResearch.WordTrace tailWord_1805018 prefixEnd_1805018 926841824017324092473879 := by
  unfold tailWord_1805018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16458603743683883344169927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43889609983157022251119805 16458603743683883344169927)
  ·
    refine ⟨24687905615525825016254891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16458603743683883344169927 24687905615525825016254891)
    ·
      refine ⟨37031858423288737524382337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24687905615525825016254891 37031858423288737524382337)
      ·
        refine ⟨27773893817466553143286753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37031858423288737524382337 27773893817466553143286753)
        ·
          refine ⟨20830420363099914857465065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27773893817466553143286753 20830420363099914857465065)
          ·
            refine ⟨15622815272324936143098799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20830420363099914857465065 15622815272324936143098799)
            ·
              refine ⟨23434222908487404214648199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15622815272324936143098799 23434222908487404214648199)
              ·
                refine ⟨35151334362731106321972299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23434222908487404214648199 35151334362731106321972299)
                ·
                  refine ⟨52727001544096659482958449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35151334362731106321972299 52727001544096659482958449)
                  ·
                    refine ⟨39545251158072494612218837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52727001544096659482958449 39545251158072494612218837)
                    ·
                      refine ⟨926841824017324092473879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39545251158072494612218837 926841824017324092473879)
                      ·
                        rfl

theorem cell23_1805018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1805018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805018 prefixEnd_1805018 := by exact prefixLift 1805018
  have htrace : WordTrace (prefixWord ++ tailWord_1805018) baseStart_1805018 baseEnd_1805018 := by
    simpa [prefixWord, tailWord_1805018, baseEnd_1805018] using wordTrace_append hprefix tailTrace_1805018
  have hstable : (prefixWord ++ tailWord_1805018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805018).length < 2 ^ (prefixWord ++ tailWord_1805018).sum := by decide
  have hdescent : baseEnd_1805018 < baseStart_1805018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805025 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 7]
def baseStart_1805025 : Nat := 118140960795 + 1805025 * 2 ^ 59
def prefixEnd_1805025 : Nat := 4983230072969 + 3 ^ 40 * 1805025 * 2
def baseEnd_1805025 : Nat := 102982824264656173898483

theorem tailTrace_1805025 : CollatzResearch.WordTrace tailWord_1805025 prefixEnd_1805025 102982824264656173898483 := by
  unfold tailWord_1805025
  simp only [CollatzResearch.WordTrace]
  refine ⟨65834670285710173572184529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43889780190473449048123019 65834670285710173572184529)
  ·
    refine ⟨49376002714282630179138397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65834670285710173572184529 49376002714282630179138397)
    ·
      refine ⟨18516001017855986317176899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49376002714282630179138397 18516001017855986317176899)
      ·
        refine ⟨27774001526783979475765349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18516001017855986317176899 27774001526783979475765349)
        ·
          refine ⟨5207625286271996151706003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27774001526783979475765349 5207625286271996151706003)
          ·
            refine ⟨7811437929407994227559005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207625286271996151706003 7811437929407994227559005)
            ·
              refine ⟨2929289223527997835334627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7811437929407994227559005 2929289223527997835334627)
              ·
                refine ⟨4393933835291996753001941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929289223527997835334627 4393933835291996753001941)
                ·
                  refine ⟨102982824264656173898483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4393933835291996753001941 102982824264656173898483)
                  ·
                    rfl

theorem cell23_1805025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 7].length) (baseStart_1805025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805025 prefixEnd_1805025 := by exact prefixLift 1805025
  have htrace : WordTrace (prefixWord ++ tailWord_1805025) baseStart_1805025 baseEnd_1805025 := by
    simpa [prefixWord, tailWord_1805025, baseEnd_1805025] using wordTrace_append hprefix tailTrace_1805025
  have hstable : (prefixWord ++ tailWord_1805025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805025).length < 2 ^ (prefixWord ++ tailWord_1805025).sum := by decide
  have hdescent : baseEnd_1805025 < baseStart_1805025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805048 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_1805048 : Nat := 118140960795 + 1805048 * 2 ^ 59
def prefixEnd_1805048 : Nat := 4983230072969 + 3 ^ 40 * 1805048 * 2
def baseEnd_1805048 : Nat := 926857228436958975098741

theorem tailTrace_1805048 : CollatzResearch.WordTrace tailWord_1805048 prefixEnd_1805048 926857228436958975098741 := by
  unfold tailWord_1805048
  simp only [CollatzResearch.WordTrace]
  refine ⟨32917754582313424250135899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43890339443084565666847865 32917754582313424250135899)
  ·
    refine ⟨49376631873470136375203849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32917754582313424250135899 49376631873470136375203849)
    ·
      refine ⟨37032473905102602281402887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49376631873470136375203849 37032473905102602281402887)
      ·
        refine ⟨55548710857653903422104331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37032473905102602281402887 55548710857653903422104331)
        ·
          refine ⟨83323066286480855133156497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55548710857653903422104331 83323066286480855133156497)
          ·
            refine ⟨62492299714860641349867373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83323066286480855133156497 62492299714860641349867373)
            ·
              refine ⟨23434612393072740506200265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62492299714860641349867373 23434612393072740506200265)
              ·
                refine ⟨17575959294804555379650199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23434612393072740506200265 17575959294804555379650199)
                ·
                  refine ⟨26363938942206833069475299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17575959294804555379650199 26363938942206833069475299)
                  ·
                    refine ⟨39545908413310249604212949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26363938942206833069475299 39545908413310249604212949)
                    ·
                      refine ⟨926857228436958975098741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39545908413310249604212949 926857228436958975098741)
                      ·
                        rfl

theorem cell23_1805048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_1805048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805048 prefixEnd_1805048 := by exact prefixLift 1805048
  have htrace : WordTrace (prefixWord ++ tailWord_1805048) baseStart_1805048 baseEnd_1805048 := by
    simpa [prefixWord, tailWord_1805048, baseEnd_1805048] using wordTrace_append hprefix tailTrace_1805048
  have hstable : (prefixWord ++ tailWord_1805048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805048).length < 2 ^ (prefixWord ++ tailWord_1805048).sum := by decide
  have hdescent : baseEnd_1805048 < baseStart_1805048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805075 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 4]
def baseStart_1805075 : Nat := 118140960795 + 1805075 * 2 ^ 59
def prefixEnd_1805075 : Nat := 4983230072969 + 3 ^ 40 * 1805075 * 2
def baseEnd_1805075 : Nat := 926871092414630369461117

theorem tailTrace_1805075 : CollatzResearch.WordTrace tailWord_1805075 prefixEnd_1805075 926871092414630369461117 := by
  unfold tailWord_1805075
  simp only [CollatzResearch.WordTrace]
  refine ⟨65836493935529032111504679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43890995957019354741003119 65836493935529032111504679)
  ·
    refine ⟨98754740903293548167257019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65836493935529032111504679 98754740903293548167257019)
    ·
      refine ⟨148132111354940322250885529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98754740903293548167257019 148132111354940322250885529)
      ·
        refine ⟨111099083516205241688164147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148132111354940322250885529 111099083516205241688164147)
        ·
          refine ⟨166648625274307862532246221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111099083516205241688164147 166648625274307862532246221)
          ·
            refine ⟨62493234477865448449592333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166648625274307862532246221 62493234477865448449592333)
            ·
              refine ⟨23434962929199543168597125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62493234477865448449592333 23434962929199543168597125)
              ·
                refine ⟨4394055549224914344111961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23434962929199543168597125 4394055549224914344111961)
                ·
                  refine ⟨3295541661918685758083971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4394055549224914344111961 3295541661918685758083971)
                  ·
                    refine ⟨4943312492878028637125957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3295541661918685758083971 4943312492878028637125957)
                    ·
                      refine ⟨926871092414630369461117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4943312492878028637125957 926871092414630369461117)
                      ·
                        rfl

theorem cell23_1805075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_1805075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805075 prefixEnd_1805075 := by exact prefixLift 1805075
  have htrace : WordTrace (prefixWord ++ tailWord_1805075) baseStart_1805075 baseEnd_1805075 := by
    simpa [prefixWord, tailWord_1805075, baseEnd_1805075] using wordTrace_append hprefix tailTrace_1805075
  have hstable : (prefixWord ++ tailWord_1805075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805075).length < 2 ^ (prefixWord ++ tailWord_1805075).sum := by decide
  have hdescent : baseEnd_1805075 < baseStart_1805075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805109 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_1805109 : Nat := 118140960795 + 1805109 * 2 ^ 59
def prefixEnd_1805109 : Nat := 4983230072969 + 3 ^ 40 * 1805109 * 2
def baseEnd_1805109 : Nat := 926888550756883236435961

theorem tailTrace_1805109 : CollatzResearch.WordTrace tailWord_1805109 prefixEnd_1805109 926888550756883236435961 := by
  unfold tailWord_1805109
  simp only [CollatzResearch.WordTrace]
  refine ⟨65837734017405855918242381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43891822678270570612161587 65837734017405855918242381)
  ·
    refine ⟨24689150256527195969340893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65837734017405855918242381 24689150256527195969340893)
    ·
      refine ⟨9258431346197698488502835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24689150256527195969340893 9258431346197698488502835)
      ·
        refine ⟨13887647019296547732754253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9258431346197698488502835 13887647019296547732754253)
        ·
          refine ⟨5207867632236205399782845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13887647019296547732754253 5207867632236205399782845)
          ·
            refine ⟨1952950362088577024918567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5207867632236205399782845 1952950362088577024918567)
            ·
              refine ⟨2929425543132865537377851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952950362088577024918567 2929425543132865537377851)
              ·
                refine ⟨4394138314699298306066777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929425543132865537377851 4394138314699298306066777)
                ·
                  refine ⟨3295603736024473729550083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4394138314699298306066777 3295603736024473729550083)
                  ·
                    refine ⟨4943405604036710594325125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3295603736024473729550083 4943405604036710594325125)
                    ·
                      refine ⟨926888550756883236435961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4943405604036710594325125 926888550756883236435961)
                      ·
                        rfl

theorem cell23_1805109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_1805109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805109 prefixEnd_1805109 := by exact prefixLift 1805109
  have htrace : WordTrace (prefixWord ++ tailWord_1805109) baseStart_1805109 baseEnd_1805109 := by
    simpa [prefixWord, tailWord_1805109, baseEnd_1805109] using wordTrace_append hprefix tailTrace_1805109
  have hstable : (prefixWord ++ tailWord_1805109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805109).length < 2 ^ (prefixWord ++ tailWord_1805109).sum := by decide
  have hdescent : baseEnd_1805109 < baseStart_1805109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805119 : List Nat := [1, 1, 2, 2, 5, 1, 1, 5, 1, 4]
def baseStart_1805119 : Nat := 118140960795 + 1805119 * 2 ^ 59
def prefixEnd_1805119 : Nat := 4983230072969 + 3 ^ 40 * 1805119 * 2
def baseEnd_1805119 : Nat := 308964561854476065770305

theorem tailTrace_1805119 : CollatzResearch.WordTrace tailWord_1805119 prefixEnd_1805119 308964561854476065770305 := by
  unfold tailWord_1805119
  simp only [CollatzResearch.WordTrace]
  refine ⟨65838098747369627626106411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43892065831579751750737607 65838098747369627626106411)
  ·
    refine ⟨98757148121054441439159617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65838098747369627626106411 98757148121054441439159617)
    ·
      refine ⟨74067861090790831079369713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98757148121054441439159617 74067861090790831079369713)
      ·
        refine ⟨55550895818093123309527285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74067861090790831079369713 55550895818093123309527285)
        ·
          refine ⟨5207896482946230310268183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55550895818093123309527285 5207896482946230310268183)
          ·
            refine ⟨7811844724419345465402275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207896482946230310268183 7811844724419345465402275)
            ·
              refine ⟨11717767086629018198103413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7811844724419345465402275 11717767086629018198103413)
              ·
                refine ⟨1098540664371470456072195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11717767086629018198103413 1098540664371470456072195)
                ·
                  refine ⟨1647810996557205684108293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098540664371470456072195 1647810996557205684108293)
                  ·
                    refine ⟨308964561854476065770305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1647810996557205684108293 308964561854476065770305)
                    ·
                      rfl

theorem cell23_1805119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 4].length) (baseStart_1805119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805119 prefixEnd_1805119 := by exact prefixLift 1805119
  have htrace : WordTrace (prefixWord ++ tailWord_1805119) baseStart_1805119 baseEnd_1805119 := by
    simpa [prefixWord, tailWord_1805119, baseEnd_1805119] using wordTrace_append hprefix tailTrace_1805119
  have hstable : (prefixWord ++ tailWord_1805119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805119).length < 2 ^ (prefixWord ++ tailWord_1805119).sum := by decide
  have hdescent : baseEnd_1805119 < baseStart_1805119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805132 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 6]
def baseStart_1805132 : Nat := 118140960795 + 1805132 * 2 ^ 59
def prefixEnd_1805132 : Nat := 4983230072969 + 3 ^ 40 * 1805132 * 2
def baseEnd_1805132 : Nat := 102988928979104071827595

theorem tailTrace_1805132 : CollatzResearch.WordTrace tailWord_1805132 prefixEnd_1805132 102988928979104071827595 := by
  unfold tailWord_1805132
  simp only [CollatzResearch.WordTrace]
  refine ⟨32919286448161265423164825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43892381930881687230886433 32919286448161265423164825)
  ·
    refine ⟨24689464836120949067373619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32919286448161265423164825 24689464836120949067373619)
    ·
      refine ⟨37034197254181423601060429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24689464836120949067373619 37034197254181423601060429)
      ·
        refine ⟨13887823970318033850397661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37034197254181423601060429 13887823970318033850397661)
        ·
          refine ⟨5207933988869262693899123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13887823970318033850397661 5207933988869262693899123)
          ·
            refine ⟨7811900983303894040848685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207933988869262693899123 7811900983303894040848685)
            ·
              refine ⟨2929462868738960265318257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7811900983303894040848685 2929462868738960265318257)
              ·
                refine ⟨2197097151554220198988693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2929462868738960265318257 2197097151554220198988693)
                ·
                  refine ⟨102988928979104071827595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2197097151554220198988693 102988928979104071827595)
                  ·
                    rfl

theorem cell23_1805132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_1805132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805132 prefixEnd_1805132 := by exact prefixLift 1805132
  have htrace : WordTrace (prefixWord ++ tailWord_1805132) baseStart_1805132 baseEnd_1805132 := by
    simpa [prefixWord, tailWord_1805132, baseEnd_1805132] using wordTrace_append hprefix tailTrace_1805132
  have hstable : (prefixWord ++ tailWord_1805132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805132).length < 2 ^ (prefixWord ++ tailWord_1805132).sum := by decide
  have hdescent : baseEnd_1805132 < baseStart_1805132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805152 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 3, 5, 2]
def baseStart_1805152 : Nat := 118140960795 + 1805152 * 2 ^ 59
def prefixEnd_1805152 : Nat := 4983230072969 + 3 ^ 40 * 1805152 * 2
def baseEnd_1805152 : Nat := 926910630425026568198263

theorem tailTrace_1805152 : CollatzResearch.WordTrace tailWord_1805152 prefixEnd_1805152 926910630425026568198263 := by
  unfold tailWord_1805152
  simp only [CollatzResearch.WordTrace]
  refine ⟨32919651178125037131028855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43892868237500049508038473 32919651178125037131028855)
  ·
    refine ⟨49379476767187555696543283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32919651178125037131028855 49379476767187555696543283)
    ·
      refine ⟨74069215150781333544814925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49379476767187555696543283 74069215150781333544814925)
      ·
        refine ⟨27775955681543000079305597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74069215150781333544814925 27775955681543000079305597)
        ·
          refine ⟨10415983380578625029739599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27775955681543000079305597 10415983380578625029739599)
          ·
            refine ⟨15623975070867937544609399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10415983380578625029739599 15623975070867937544609399)
            ·
              refine ⟨23435962606301906316914099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15623975070867937544609399 23435962606301906316914099)
              ·
                refine ⟨35153943909452859475371149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23435962606301906316914099 35153943909452859475371149)
                ·
                  refine ⟨13182728966044822303264181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35153943909452859475371149 13182728966044822303264181)
                  ·
                    refine ⟨1235880840566702090931017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13182728966044822303264181 1235880840566702090931017)
                    ·
                      refine ⟨926910630425026568198263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235880840566702090931017 926910630425026568198263)
                      ·
                        rfl

theorem cell23_1805152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_1805152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805152 prefixEnd_1805152 := by exact prefixLift 1805152
  have htrace : WordTrace (prefixWord ++ tailWord_1805152) baseStart_1805152 baseEnd_1805152 := by
    simpa [prefixWord, tailWord_1805152, baseEnd_1805152] using wordTrace_append hprefix tailTrace_1805152
  have hstable : (prefixWord ++ tailWord_1805152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805152).length < 2 ^ (prefixWord ++ tailWord_1805152).sum := by decide
  have hdescent : baseEnd_1805152 < baseStart_1805152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805159 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_1805159 : Nat := 118140960795 + 1805159 * 2 ^ 59
def prefixEnd_1805159 : Nat := 4983230072969 + 3 ^ 40 * 1805159 * 2
def baseEnd_1805159 : Nat := 926914224789608040810731

theorem tailTrace_1805159 : CollatzResearch.WordTrace tailWord_1805159 prefixEnd_1805159 926914224789608040810731 := by
  unfold tailWord_1805159
  simp only [CollatzResearch.WordTrace]
  refine ⟨65839557667224714457562531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43893038444816476305041687 65839557667224714457562531)
  ·
    refine ⟨98759336500837071686343797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65839557667224714457562531 98759336500837071686343797)
    ·
      refine ⟨9258687796953475470594731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98759336500837071686343797 9258687796953475470594731)
      ·
        refine ⟨13888031695430213205892097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9258687796953475470594731 13888031695430213205892097)
        ·
          refine ⟨10416023771572659904419073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13888031695430213205892097 10416023771572659904419073)
          ·
            refine ⟨7812017828679494928314305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10416023771572659904419073 7812017828679494928314305)
            ·
              refine ⟨5859013371509621196235729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7812017828679494928314305 5859013371509621196235729)
              ·
                refine ⟨4394260028632215897176797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5859013371509621196235729 4394260028632215897176797)
                ·
                  refine ⟨1647847510737080961441299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4394260028632215897176797 1647847510737080961441299)
                  ·
                    refine ⟨2471771266105621442161949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1647847510737080961441299 2471771266105621442161949)
                    ·
                      refine ⟨926914224789608040810731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2471771266105621442161949 926914224789608040810731)
                      ·
                        rfl

theorem cell23_1805159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_1805159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805159 prefixEnd_1805159 := by exact prefixLift 1805159
  have htrace : WordTrace (prefixWord ++ tailWord_1805159) baseStart_1805159 baseEnd_1805159 := by
    simpa [prefixWord, tailWord_1805159, baseEnd_1805159] using wordTrace_append hprefix tailTrace_1805159
  have hstable : (prefixWord ++ tailWord_1805159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805159).length < 2 ^ (prefixWord ++ tailWord_1805159).sum := by decide
  have hdescent : baseEnd_1805159 < baseStart_1805159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805175 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 1, 6]
def baseStart_1805175 : Nat := 118140960795 + 1805175 * 2 ^ 59
def prefixEnd_1805175 : Nat := 4983230072969 + 3 ^ 40 * 1805175 * 2
def baseEnd_1805175 : Nat := 308974146826693326070219

theorem tailTrace_1805175 : CollatzResearch.WordTrace tailWord_1805175 prefixEnd_1805175 308974146826693326070219 := by
  unfold tailWord_1805175
  simp only [CollatzResearch.WordTrace]
  refine ⟨65840141235166749190144979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43893427490111166126763319 65840141235166749190144979)
  ·
    refine ⟨98760211852750123785217469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65840141235166749190144979 98760211852750123785217469)
    ·
      refine ⟨37035079444781296419456551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98760211852750123785217469 37035079444781296419456551)
      ·
        refine ⟨55552619167171944629184827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37035079444781296419456551 55552619167171944629184827)
        ·
          refine ⟨83328928750757916943777241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55552619167171944629184827 83328928750757916943777241)
          ·
            refine ⟨62496696563068437707832931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83328928750757916943777241 62496696563068437707832931)
            ·
              refine ⟨93745044844602656561749397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62496696563068437707832931 93745044844602656561749397)
              ·
                refine ⟨4394298977090749526332003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93745044844602656561749397 4394298977090749526332003)
                ·
                  refine ⟨6591448465636124289498005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394298977090749526332003 6591448465636124289498005)
                  ·
                    refine ⟨308974146826693326070219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6591448465636124289498005 308974146826693326070219)
                    ·
                      rfl

theorem cell23_1805175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_1805175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805175 prefixEnd_1805175 := by exact prefixLift 1805175
  have htrace : WordTrace (prefixWord ++ tailWord_1805175) baseStart_1805175 baseEnd_1805175 := by
    simpa [prefixWord, tailWord_1805175, baseEnd_1805175] using wordTrace_append hprefix tailTrace_1805175
  have hstable : (prefixWord ++ tailWord_1805175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805175).length < 2 ^ (prefixWord ++ tailWord_1805175).sum := by decide
  have hdescent : baseEnd_1805175 < baseStart_1805175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805193 : List Nat := [1, 2, 1, 1, 5, 3, 3, 2, 1, 1, 3]
def baseStart_1805193 : Nat := 118140960795 + 1805193 * 2 ^ 59
def prefixEnd_1805193 : Nat := 4983230072969 + 3 ^ 40 * 1805193 * 2
def baseEnd_1805193 : Nat := 926931683131860907785575

theorem tailTrace_1805193 : CollatzResearch.WordTrace tailWord_1805193 prefixEnd_1805193 926931683131860907785575 := by
  unfold tailWord_1805193
  simp only [CollatzResearch.WordTrace]
  refine ⟨65840797749101538264300233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43893865166067692176200155 65840797749101538264300233)
  ·
    refine ⟨49380598311826153698225175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65840797749101538264300233 49380598311826153698225175)
    ·
      refine ⟨74070897467739230547337763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49380598311826153698225175 74070897467739230547337763)
      ·
        refine ⟨111106346201608845821006645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74070897467739230547337763 111106346201608845821006645)
        ·
          refine ⟨10416219956400829295719373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111106346201608845821006645 10416219956400829295719373)
          ·
            refine ⟨3906082483650310985894765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10416219956400829295719373 3906082483650310985894765)
            ·
              refine ⟨1464780931368866619710537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3906082483650310985894765 1464780931368866619710537)
              ·
                refine ⟨1098585698526649964782903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1464780931368866619710537 1098585698526649964782903)
                ·
                  refine ⟨1647878547789974947174355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098585698526649964782903 1647878547789974947174355)
                  ·
                    refine ⟨2471817821684962420761533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1647878547789974947174355 2471817821684962420761533)
                    ·
                      refine ⟨926931683131860907785575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2471817821684962420761533 926931683131860907785575)
                      ·
                        rfl

theorem cell23_1805193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 1, 3].length) (baseStart_1805193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805193 prefixEnd_1805193 := by exact prefixLift 1805193
  have htrace : WordTrace (prefixWord ++ tailWord_1805193) baseStart_1805193 baseEnd_1805193 := by
    simpa [prefixWord, tailWord_1805193, baseEnd_1805193] using wordTrace_append hprefix tailTrace_1805193
  have hstable : (prefixWord ++ tailWord_1805193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805193).length < 2 ^ (prefixWord ++ tailWord_1805193).sum := by decide
  have hdescent : baseEnd_1805193 < baseStart_1805193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805195 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 6]
def baseStart_1805195 : Nat := 118140960795 + 1805195 * 2 ^ 59
def prefixEnd_1805195 : Nat := 4983230072969 + 3 ^ 40 * 1805195 * 2
def baseEnd_1805195 : Nat := 926932710093169899960565

theorem tailTrace_1805195 : CollatzResearch.WordTrace tailWord_1805195 prefixEnd_1805195 926932710093169899960565 := by
  unfold tailWord_1805195
  simp only [CollatzResearch.WordTrace]
  refine ⟨65840870695094292605873039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43893913796729528403915359 65840870695094292605873039)
  ·
    refine ⟨98761306042641438908809559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65840870695094292605873039 98761306042641438908809559)
    ·
      refine ⟨148141959063962158363214339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98761306042641438908809559 148141959063962158363214339)
      ·
        refine ⟨222212938595943237544821509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148141959063962158363214339 222212938595943237544821509)
        ·
          refine ⟨41664925986739357039654033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222212938595943237544821509 41664925986739357039654033)
          ·
            refine ⟨31248694490054517779740525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41664925986739357039654033 31248694490054517779740525)
            ·
              refine ⟨11718260433770444167402697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31248694490054517779740525 11718260433770444167402697)
              ·
                refine ⟨8788695325327833125552023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11718260433770444167402697 8788695325327833125552023)
                ·
                  refine ⟨13183042987991749688328035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8788695325327833125552023 13183042987991749688328035)
                  ·
                    refine ⟨19774564481987624532492053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13183042987991749688328035 19774564481987624532492053)
                    ·
                      refine ⟨926932710093169899960565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19774564481987624532492053 926932710093169899960565)
                      ·
                        rfl

theorem cell23_1805195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_1805195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805195 prefixEnd_1805195 := by exact prefixLift 1805195
  have htrace : WordTrace (prefixWord ++ tailWord_1805195) baseStart_1805195 baseEnd_1805195 := by
    simpa [prefixWord, tailWord_1805195, baseEnd_1805195] using wordTrace_append hprefix tailTrace_1805195
  have hstable : (prefixWord ++ tailWord_1805195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805195).length < 2 ^ (prefixWord ++ tailWord_1805195).sum := by decide
  have hdescent : baseEnd_1805195 < baseStart_1805195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805205 : List Nat := [1, 3, 2, 1, 1, 4, 1, 10]
def baseStart_1805205 : Nat := 118140960795 + 1805205 * 2 ^ 59
def prefixEnd_1805205 : Nat := 4983230072969 + 3 ^ 40 * 1805205 * 2
def baseEnd_1805205 : Nat := 34331031292582031882797

theorem tailTrace_1805205 : CollatzResearch.WordTrace tailWord_1805205 prefixEnd_1805205 34331031292582031882797 := by
  unfold tailWord_1805205
  simp only [CollatzResearch.WordTrace]
  refine ⟨65841235425058064313737069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43894156950038709542491379 65841235425058064313737069)
  ·
    refine ⟨24690463284396774117651401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65841235425058064313737069 24690463284396774117651401)
    ·
      refine ⟨18517847463297580588238551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24690463284396774117651401 18517847463297580588238551)
      ·
        refine ⟨27776771194946370882357827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18517847463297580588238551 27776771194946370882357827)
        ·
          refine ⟨41665156792419556323536741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27776771194946370882357827 41665156792419556323536741)
          ·
            refine ⟨7812216898578666810663139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41665156792419556323536741 7812216898578666810663139)
            ·
              refine ⟨11718325347868000215994709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7812216898578666810663139 11718325347868000215994709)
              ·
                refine ⟨34331031292582031882797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11718325347868000215994709 34331031292582031882797)
                ·
                  rfl

theorem cell23_1805205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 10].length) (baseStart_1805205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805205 prefixEnd_1805205 := by exact prefixLift 1805205
  have htrace : WordTrace (prefixWord ++ tailWord_1805205) baseStart_1805205 baseEnd_1805205 := by
    simpa [prefixWord, tailWord_1805205, baseEnd_1805205] using wordTrace_append hprefix tailTrace_1805205
  have hstable : (prefixWord ++ tailWord_1805205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805205).length < 2 ^ (prefixWord ++ tailWord_1805205).sum := by decide
  have hdescent : baseEnd_1805205 < baseStart_1805205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805219 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 3]
def baseStart_1805219 : Nat := 118140960795 + 1805219 * 2 ^ 59
def prefixEnd_1805219 : Nat := 4983230072969 + 3 ^ 40 * 1805219 * 2
def baseEnd_1805219 : Nat := 926945033628877806060455

theorem tailTrace_1805219 : CollatzResearch.WordTrace tailWord_1805219 prefixEnd_1805219 926945033628877806060455 := by
  unfold tailWord_1805219
  simp only [CollatzResearch.WordTrace]
  refine ⟨65841746047007344704746711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43894497364671563136497807 65841746047007344704746711)
  ·
    refine ⟨98762619070511017057120067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65841746047007344704746711 98762619070511017057120067)
    ·
      refine ⟨148143928605766525585680101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98762619070511017057120067 148143928605766525585680101)
      ·
        refine ⟨27776986613581223547315019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148143928605766525585680101 27776986613581223547315019)
        ·
          refine ⟨41665479920371835320972529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27776986613581223547315019 41665479920371835320972529)
          ·
            refine ⟨31249109940278876490729397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41665479920371835320972529 31249109940278876490729397)
            ·
              refine ⟨2929604056901144671005881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31249109940278876490729397 2929604056901144671005881)
              ·
                refine ⟨2197203042675858503254411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2929604056901144671005881 2197203042675858503254411)
                ·
                  refine ⟨3295804564013787754881617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197203042675858503254411 3295804564013787754881617)
                  ·
                    refine ⟨2471853423010340816161213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3295804564013787754881617 2471853423010340816161213)
                    ·
                      refine ⟨926945033628877806060455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2471853423010340816161213 926945033628877806060455)
                      ·
                        rfl

theorem cell23_1805219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_1805219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805219 prefixEnd_1805219 := by exact prefixLift 1805219
  have htrace : WordTrace (prefixWord ++ tailWord_1805219) baseStart_1805219 baseEnd_1805219 := by
    simpa [prefixWord, tailWord_1805219, baseEnd_1805219] using wordTrace_append hprefix tailTrace_1805219
  have hstable : (prefixWord ++ tailWord_1805219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805219).length < 2 ^ (prefixWord ++ tailWord_1805219).sum := by decide
  have hdescent : baseEnd_1805219 < baseStart_1805219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805236 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1805236 : Nat := 118140960795 + 1805236 * 2 ^ 59
def prefixEnd_1805236 : Nat := 4983230072969 + 3 ^ 40 * 1805236 * 2
def baseEnd_1805236 : Nat := 926953762800004239547877

theorem tailTrace_1805236 : CollatzResearch.WordTrace tailWord_1805236 prefixEnd_1805236 926953762800004239547877 := by
  unfold tailWord_1805236
  simp only [CollatzResearch.WordTrace]
  refine ⟨32921183043972878304057781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43894910725297171072077041 32921183043972878304057781)
  ·
    refine ⟨3086360910372457341005417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32921183043972878304057781 3086360910372457341005417)
    ·
      refine ⟨2314770682779343005754063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3086360910372457341005417 2314770682779343005754063)
      ·
        refine ⟨3472156024169014508631095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314770682779343005754063 3472156024169014508631095)
        ·
          refine ⟨5208234036253521762946643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472156024169014508631095 5208234036253521762946643)
          ·
            refine ⟨7812351054380282644419965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208234036253521762946643 7812351054380282644419965)
            ·
              refine ⟨2929631645392605991657487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7812351054380282644419965 2929631645392605991657487)
              ·
                refine ⟨4394447468088908987486231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929631645392605991657487 4394447468088908987486231)
                ·
                  refine ⟨6591671202133363481229347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394447468088908987486231 6591671202133363481229347)
                  ·
                    refine ⟨9887506803200045221844021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6591671202133363481229347 9887506803200045221844021)
                    ·
                      refine ⟨926953762800004239547877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9887506803200045221844021 926953762800004239547877)
                      ·
                        rfl

theorem cell23_1805236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1805236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805236 prefixEnd_1805236 := by exact prefixLift 1805236
  have htrace : WordTrace (prefixWord ++ tailWord_1805236) baseStart_1805236 baseEnd_1805236 := by
    simpa [prefixWord, tailWord_1805236, baseEnd_1805236] using wordTrace_append hprefix tailTrace_1805236
  have hstable : (prefixWord ++ tailWord_1805236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805236).length < 2 ^ (prefixWord ++ tailWord_1805236).sum := by decide
  have hdescent : baseEnd_1805236 < baseStart_1805236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805259 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 3, 3, 2]
def baseStart_1805259 : Nat := 118140960795 + 1805259 * 2 ^ 59
def prefixEnd_1805259 : Nat := 4983230072969 + 3 ^ 40 * 1805259 * 2
def baseEnd_1805259 : Nat := 926965572855057649560271

theorem tailTrace_1805259 : CollatzResearch.WordTrace tailWord_1805259 prefixEnd_1805259 926965572855057649560271 := by
  unfold tailWord_1805259
  simp only [CollatzResearch.WordTrace]
  refine ⟨65843204966862431536202831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43895469977908287690801887 65843204966862431536202831)
  ·
    refine ⟨98764807450293647304304247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65843204966862431536202831 98764807450293647304304247)
    ·
      refine ⟨148147211175440470956456371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98764807450293647304304247 148147211175440470956456371)
      ·
        refine ⟨222220816763160706434684557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148147211175440470956456371 222220816763160706434684557)
        ·
          refine ⟨83332806286185264913006709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222220816763160706434684557 83332806286185264913006709)
          ·
            refine ⟨7812450589329868585594379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83332806286185264913006709 7812450589329868585594379)
            ·
              refine ⟨11718675883994802878391569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7812450589329868585594379 11718675883994802878391569)
              ·
                refine ⟨8789006912996102158793677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11718675883994802878391569 8789006912996102158793677)
                ·
                  refine ⟨3295877592373538309547629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8789006912996102158793677 3295877592373538309547629)
                  ·
                    refine ⟨1235954097140076866080361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295877592373538309547629 1235954097140076866080361)
                    ·
                      refine ⟨926965572855057649560271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1235954097140076866080361 926965572855057649560271)
                      ·
                        rfl

theorem cell23_1805259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 3, 2].length) (baseStart_1805259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805259 prefixEnd_1805259 := by exact prefixLift 1805259
  have htrace : WordTrace (prefixWord ++ tailWord_1805259) baseStart_1805259 baseEnd_1805259 := by
    simpa [prefixWord, tailWord_1805259, baseEnd_1805259] using wordTrace_append hprefix tailTrace_1805259
  have hstable : (prefixWord ++ tailWord_1805259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805259).length < 2 ^ (prefixWord ++ tailWord_1805259).sum := by decide
  have hdescent : baseEnd_1805259 < baseStart_1805259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805266 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1805266 : Nat := 118140960795 + 1805266 * 2 ^ 59
def prefixEnd_1805266 : Nat := 4983230072969 + 3 ^ 40 * 1805266 * 2
def baseEnd_1805266 : Nat := 926969167219639122172739

theorem tailTrace_1805266 : CollatzResearch.WordTrace tailWord_1805266 prefixEnd_1805266 926969167219639122172739 := by
  unfold tailWord_1805266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16460865069459267932926913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43895640185224714487805101 16460865069459267932926913)
  ·
    refine ⟨12345648802094450949695185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16460865069459267932926913 12345648802094450949695185)
    ·
      refine ⟨9259236601570838212271389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12345648802094450949695185 9259236601570838212271389)
      ·
        refine ⟨3472213725589064329601771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9259236601570838212271389 3472213725589064329601771)
        ·
          refine ⟨5208320588383596494402657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472213725589064329601771 5208320588383596494402657)
          ·
            refine ⟨3906240441287697370801993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5208320588383596494402657 3906240441287697370801993)
            ·
              refine ⟨2929680330965773028101495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3906240441287697370801993 2929680330965773028101495)
              ·
                refine ⟨4394520496448659542152243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929680330965773028101495 4394520496448659542152243)
                ·
                  refine ⟨6591780744672989313228365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394520496448659542152243 6591780744672989313228365)
                  ·
                    refine ⟨2471917779252370992460637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6591780744672989313228365 2471917779252370992460637)
                    ·
                      refine ⟨926969167219639122172739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2471917779252370992460637 926969167219639122172739)
                      ·
                        rfl

theorem cell23_1805266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1805266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805266 prefixEnd_1805266 := by exact prefixLift 1805266
  have htrace : WordTrace (prefixWord ++ tailWord_1805266) baseStart_1805266 baseEnd_1805266 := by
    simpa [prefixWord, tailWord_1805266, baseEnd_1805266] using wordTrace_append hprefix tailTrace_1805266
  have hstable : (prefixWord ++ tailWord_1805266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805266).length < 2 ^ (prefixWord ++ tailWord_1805266).sum := by decide
  have hdescent : baseEnd_1805266 < baseStart_1805266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805346 : List Nat := [3, 3, 1, 1, 1, 3, 3, 3, 5]
def baseStart_1805346 : Nat := 118140960795 + 1805346 * 2 ^ 59
def prefixEnd_1805346 : Nat := 4983230072969 + 3 ^ 40 * 1805346 * 2
def baseEnd_1805346 : Nat := 103001138407999867685819

theorem tailTrace_1805346 : CollatzResearch.WordTrace tailWord_1805346 prefixEnd_1805346 103001138407999867685819 := by
  unfold tailWord_1805346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16461594529386811348654973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43897585411698163596413261 16461594529386811348654973)
  ·
    refine ⟨6173097948520054255745615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16461594529386811348654973 6173097948520054255745615)
    ·
      refine ⟨9259646922780081383618423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6173097948520054255745615 9259646922780081383618423)
      ·
        refine ⟨13889470384170122075427635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9259646922780081383618423 13889470384170122075427635)
        ·
          refine ⟨20834205576255183113141453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13889470384170122075427635 20834205576255183113141453)
          ·
            refine ⟨7812827091095693667428045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20834205576255183113141453 7812827091095693667428045)
            ·
              refine ⟨2929810159160885125285517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7812827091095693667428045 2929810159160885125285517)
              ·
                refine ⟨1098678809685331921982069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2929810159160885125285517 1098678809685331921982069)
                ·
                  refine ⟨103001138407999867685819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1098678809685331921982069 103001138407999867685819)
                  ·
                    rfl

theorem cell23_1805346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_1805346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805346 prefixEnd_1805346 := by exact prefixLift 1805346
  have htrace : WordTrace (prefixWord ++ tailWord_1805346) baseStart_1805346 baseEnd_1805346 := by
    simpa [prefixWord, tailWord_1805346, baseEnd_1805346] using wordTrace_append hprefix tailTrace_1805346
  have hstable : (prefixWord ++ tailWord_1805346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805346).length < 2 ^ (prefixWord ++ tailWord_1805346).sum := by decide
  have hdescent : baseEnd_1805346 < baseStart_1805346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805369 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1805369 : Nat := 118140960795 + 1805369 * 2 ^ 59
def prefixEnd_1805369 : Nat := 4983230072969 + 3 ^ 40 * 1805369 * 2
def baseEnd_1805369 : Nat := 927022055727052219184765

theorem tailTrace_1805369 : CollatzResearch.WordTrace tailWord_1805369 prefixEnd_1805369 927022055727052219184765 := by
  unfold tailWord_1805369
  simp only [CollatzResearch.WordTrace]
  refine ⟨65847216996463920322707161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43898144664309280215138107 65847216996463920322707161)
  ·
    refine ⟨49385412747347940242030371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65847216996463920322707161 49385412747347940242030371)
    ·
      refine ⟨74078119121021910363045557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49385412747347940242030371 74078119121021910363045557)
      ·
        refine ⟨6944823667595804096535521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74078119121021910363045557 6944823667595804096535521)
        ·
          refine ⟨5208617750696853072401641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6944823667595804096535521 5208617750696853072401641)
          ·
            refine ⟨3906463313022639804301231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5208617750696853072401641 3906463313022639804301231)
            ·
              refine ⟨5859694969533959706451847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906463313022639804301231 5859694969533959706451847)
              ·
                refine ⟨8789542454300939559677771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859694969533959706451847 8789542454300939559677771)
                ·
                  refine ⟨13184313681451409339516657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8789542454300939559677771 13184313681451409339516657)
                  ·
                    refine ⟨9888235261088557004637493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13184313681451409339516657 9888235261088557004637493)
                    ·
                      refine ⟨927022055727052219184765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9888235261088557004637493 927022055727052219184765)
                      ·
                        rfl

theorem cell23_1805369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1805369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805369 prefixEnd_1805369 := by exact prefixLift 1805369
  have htrace : WordTrace (prefixWord ++ tailWord_1805369) baseStart_1805369 baseEnd_1805369 := by
    simpa [prefixWord, tailWord_1805369, baseEnd_1805369] using wordTrace_append hprefix tailTrace_1805369
  have hstable : (prefixWord ++ tailWord_1805369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805369).length < 2 ^ (prefixWord ++ tailWord_1805369).sum := by decide
  have hdescent : baseEnd_1805369 < baseStart_1805369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805379 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 1, 6, 2]
def baseStart_1805379 : Nat := 118140960795 + 1805379 * 2 ^ 59
def prefixEnd_1805379 : Nat := 4983230072969 + 3 ^ 40 * 1805379 * 2
def baseEnd_1805379 : Nat := 927027190533597180059719

theorem tailTrace_1805379 : CollatzResearch.WordTrace tailWord_1805379 prefixEnd_1805379 927027190533597180059719 := by
  unfold tailWord_1805379
  simp only [CollatzResearch.WordTrace]
  refine ⟨65847581726427692030571191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43898387817618461353714127 65847581726427692030571191)
  ·
    refine ⟨98771372589641538045856787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65847581726427692030571191 98771372589641538045856787)
    ·
      refine ⟨148157058884462307068785181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98771372589641538045856787 148157058884462307068785181)
      ·
        refine ⟨55558897081673365150794443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148157058884462307068785181 55558897081673365150794443)
        ·
          refine ⟨83338345622510047726191665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55558897081673365150794443 83338345622510047726191665)
          ·
            refine ⟨62503759216882535794643749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83338345622510047726191665 62503759216882535794643749)
            ·
              refine ⟨11719454853165475461495703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62503759216882535794643749 11719454853165475461495703)
              ·
                refine ⟨17579182279748213192243555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11719454853165475461495703 17579182279748213192243555)
                ·
                  refine ⟨26368773419622319788365333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17579182279748213192243555 26368773419622319788365333)
                  ·
                    refine ⟨1236036254044796240079625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26368773419622319788365333 1236036254044796240079625)
                    ·
                      refine ⟨927027190533597180059719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1236036254044796240079625 927027190533597180059719)
                      ·
                        rfl

theorem cell23_1805379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_1805379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805379 prefixEnd_1805379 := by exact prefixLift 1805379
  have htrace : WordTrace (prefixWord ++ tailWord_1805379) baseStart_1805379 baseEnd_1805379 := by
    simpa [prefixWord, tailWord_1805379, baseEnd_1805379] using wordTrace_append hprefix tailTrace_1805379
  have hstable : (prefixWord ++ tailWord_1805379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805379).length < 2 ^ (prefixWord ++ tailWord_1805379).sum := by decide
  have hdescent : baseEnd_1805379 < baseStart_1805379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805392 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_1805392 : Nat := 118140960795 + 1805392 * 2 ^ 59
def prefixEnd_1805392 : Nat := 4983230072969 + 3 ^ 40 * 1805392 * 2
def baseEnd_1805392 : Nat := 927033865782105629197159

theorem tailTrace_1805392 : CollatzResearch.WordTrace tailWord_1805392 prefixEnd_1805392 927033865782105629197159 := by
  unfold tailWord_1805392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32924027937690297625397215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43898703916920396833862953 32924027937690297625397215)
  ·
    refine ⟨49386041906535446438095823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32924027937690297625397215 49386041906535446438095823)
    ·
      refine ⟨74079062859803169657143735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49386041906535446438095823 74079062859803169657143735)
      ·
        refine ⟨111118594289704754485715603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74079062859803169657143735 111118594289704754485715603)
        ·
          refine ⟨166677891434557131728573405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111118594289704754485715603 166677891434557131728573405)
          ·
            refine ⟨62504209287958924398215027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166677891434557131728573405 62504209287958924398215027)
            ·
              refine ⟨93756313931938386597322541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62504209287958924398215027 93756313931938386597322541)
              ·
                refine ⟨35158617724476894973995953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93756313931938386597322541 35158617724476894973995953)
                ·
                  refine ⟨26368963293357671230496965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35158617724476894973995953 26368963293357671230496965)
                  ·
                    refine ⟨4944180617504563355718181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26368963293357671230496965 4944180617504563355718181)
                    ·
                      refine ⟨927033865782105629197159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4944180617504563355718181 927033865782105629197159)
                      ·
                        rfl

theorem cell23_1805392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_1805392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805392 prefixEnd_1805392 := by exact prefixLift 1805392
  have htrace : WordTrace (prefixWord ++ tailWord_1805392) baseStart_1805392 baseEnd_1805392 := by
    simpa [prefixWord, tailWord_1805392, baseEnd_1805392] using wordTrace_append hprefix tailTrace_1805392
  have hstable : (prefixWord ++ tailWord_1805392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805392).length < 2 ^ (prefixWord ++ tailWord_1805392).sum := by decide
  have hdescent : baseEnd_1805392 < baseStart_1805392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805402 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 8]
def baseStart_1805402 : Nat := 118140960795 + 1805402 * 2 ^ 59
def prefixEnd_1805402 : Nat := 4983230072969 + 3 ^ 40 * 1805402 * 2
def baseEnd_1805402 : Nat := 103004333398738954452457

theorem tailTrace_1805402 : CollatzResearch.WordTrace tailWord_1805402 prefixEnd_1805402 103004333398738954452457 := by
  unfold tailWord_1805402
  simp only [CollatzResearch.WordTrace]
  refine ⟨16462105151336091739664615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43898947070229577972438973 16462105151336091739664615)
  ·
    refine ⟨24693157727004137609496923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16462105151336091739664615 24693157727004137609496923)
    ·
      refine ⟨37039736590506206414245385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24693157727004137609496923 37039736590506206414245385)
      ·
        refine ⟨27779802442879654810684039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37039736590506206414245385 27779802442879654810684039)
        ·
          refine ⟨41669703664319482216026059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27779802442879654810684039 41669703664319482216026059)
          ·
            refine ⟨62504555496479223324039089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41669703664319482216026059 62504555496479223324039089)
            ·
              refine ⟨46878416622359417493029317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62504555496479223324039089 46878416622359417493029317)
              ·
                refine ⟨8789703116692390779942997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46878416622359417493029317 8789703116692390779942997)
                ·
                  refine ⟨103004333398738954452457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8789703116692390779942997 103004333398738954452457)
                  ·
                    rfl

theorem cell23_1805402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_1805402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805402 prefixEnd_1805402 := by exact prefixLift 1805402
  have htrace : WordTrace (prefixWord ++ tailWord_1805402) baseStart_1805402 baseEnd_1805402 := by
    simpa [prefixWord, tailWord_1805402, baseEnd_1805402] using wordTrace_append hprefix tailTrace_1805402
  have hstable : (prefixWord ++ tailWord_1805402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805402).length < 2 ^ (prefixWord ++ tailWord_1805402).sum := by decide
  have hdescent : baseEnd_1805402 < baseStart_1805402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805449 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 3, 5]
def baseStart_1805449 : Nat := 118140960795 + 1805449 * 2 ^ 59
def prefixEnd_1805449 : Nat := 4983230072969 + 3 ^ 40 * 1805449 * 2
def baseEnd_1805449 : Nat := 309021044726470635394799

theorem tailTrace_1805449 : CollatzResearch.WordTrace tailWord_1805449 prefixEnd_1805449 309021044726470635394799 := by
  unfold tailWord_1805449
  simp only [CollatzResearch.WordTrace]
  refine ⟨65850134836174093985619401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43900089890782729323746267 65850134836174093985619401)
  ·
    refine ⟨49387601127130570489214551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65850134836174093985619401 49387601127130570489214551)
    ·
      refine ⟨74081401690695855733821827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49387601127130570489214551 74081401690695855733821827)
      ·
        refine ⟨111122102536043783600732741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74081401690695855733821827 111122102536043783600732741)
        ·
          refine ⟨20835394225508209425137389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111122102536043783600732741 20835394225508209425137389)
          ·
            refine ⟨7813272834565578534426521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20835394225508209425137389 7813272834565578534426521)
            ·
              refine ⟨5859954625924183900819891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7813272834565578534426521 5859954625924183900819891)
              ·
                refine ⟨8789931938886275851229837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859954625924183900819891 8789931938886275851229837)
                ·
                  refine ⟨3296224477082353444211189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8789931938886275851229837 3296224477082353444211189)
                  ·
                    refine ⟨309021044726470635394799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3296224477082353444211189 309021044726470635394799)
                    ·
                      rfl

theorem cell23_1805449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_1805449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805449 prefixEnd_1805449 := by exact prefixLift 1805449
  have htrace : WordTrace (prefixWord ++ tailWord_1805449) baseStart_1805449 baseEnd_1805449 := by
    simpa [prefixWord, tailWord_1805449, baseEnd_1805449] using wordTrace_append hprefix tailTrace_1805449
  have hstable : (prefixWord ++ tailWord_1805449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805449).length < 2 ^ (prefixWord ++ tailWord_1805449).sum := by decide
  have hdescent : baseEnd_1805449 < baseStart_1805449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805456 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 2, 3, 2]
def baseStart_1805456 : Nat := 118140960795 + 1805456 * 2 ^ 59
def prefixEnd_1805456 : Nat := 4983230072969 + 3 ^ 40 * 1805456 * 2
def baseEnd_1805456 : Nat := 927066728543993378796865

theorem tailTrace_1805456 : CollatzResearch.WordTrace tailWord_1805456 prefixEnd_1805456 927066728543993378796865 := by
  unfold tailWord_1805456
  simp only [CollatzResearch.WordTrace]
  refine ⟨32925195073574367090562111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43900260098099156120749481 32925195073574367090562111)
  ·
    refine ⟨49387792610361550635843167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32925195073574367090562111 49387792610361550635843167)
    ·
      refine ⟨74081688915542325953764751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49387792610361550635843167 74081688915542325953764751)
      ·
        refine ⟨111122533373313488930647127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74081688915542325953764751 111122533373313488930647127)
        ·
          refine ⟨166683800059970233395970691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111122533373313488930647127 166683800059970233395970691)
          ·
            refine ⟨250025700089955350093956037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166683800059970233395970691 250025700089955350093956037)
            ·
              refine ⟨46879818766866628142616757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250025700089955350093956037 46879818766866628142616757)
              ·
                refine ⟨4394983009393746388370321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46879818766866628142616757 4394983009393746388370321)
                ·
                  refine ⟨3296237257045309791277741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4394983009393746388370321 3296237257045309791277741)
                  ·
                    refine ⟨1236088971391991171729153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296237257045309791277741 1236088971391991171729153)
                    ·
                      refine ⟨927066728543993378796865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1236088971391991171729153 927066728543993378796865)
                      ·
                        rfl

theorem cell23_1805456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 3, 2].length) (baseStart_1805456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805456 prefixEnd_1805456 := by exact prefixLift 1805456
  have htrace : WordTrace (prefixWord ++ tailWord_1805456) baseStart_1805456 baseEnd_1805456 := by
    simpa [prefixWord, tailWord_1805456, baseEnd_1805456] using wordTrace_append hprefix tailTrace_1805456
  have hstable : (prefixWord ++ tailWord_1805456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805456).length < 2 ^ (prefixWord ++ tailWord_1805456).sum := by decide
  have hdescent : baseEnd_1805456 < baseStart_1805456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805499 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 4]
def baseStart_1805499 : Nat := 118140960795 + 1805499 * 2 ^ 59
def prefixEnd_1805499 : Nat := 4983230072969 + 3 ^ 40 * 1805499 * 2
def baseEnd_1805499 : Nat := 927088808212136710559167

theorem tailTrace_1805499 : CollatzResearch.WordTrace tailWord_1805499 prefixEnd_1805499 927088808212136710559167 := by
  unfold tailWord_1805499
  simp only [CollatzResearch.WordTrace]
  refine ⟨65851958485992952524939551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43901305657328635016626367 65851958485992952524939551)
  ·
    refine ⟨98777937728989428787409327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65851958485992952524939551 98777937728989428787409327)
    ·
      refine ⟨148166906593484143181113991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98777937728989428787409327 148166906593484143181113991)
      ·
        refine ⟨222250359890226214771670987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148166906593484143181113991 222250359890226214771670987)
        ·
          refine ⟨333375539835339322157506481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222250359890226214771670987 333375539835339322157506481)
          ·
            refine ⟨250031654876504491618129861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333375539835339322157506481 250031654876504491618129861)
            ·
              refine ⟨46880935289344592178399349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250031654876504491618129861 46880935289344592178399349)
              ·
                refine ⟨4395087683376055516724939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46880935289344592178399349 4395087683376055516724939)
                ·
                  refine ⟨6592631525064083275087409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395087683376055516724939 6592631525064083275087409)
                  ·
                    refine ⟨4944473643798062456315557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6592631525064083275087409 4944473643798062456315557)
                    ·
                      refine ⟨927088808212136710559167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4944473643798062456315557 927088808212136710559167)
                      ·
                        rfl

theorem cell23_1805499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 4].length) (baseStart_1805499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805499 prefixEnd_1805499 := by exact prefixLift 1805499
  have htrace : WordTrace (prefixWord ++ tailWord_1805499) baseStart_1805499 baseEnd_1805499 := by
    simpa [prefixWord, tailWord_1805499, baseEnd_1805499] using wordTrace_append hprefix tailTrace_1805499
  have hstable : (prefixWord ++ tailWord_1805499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805499).length < 2 ^ (prefixWord ++ tailWord_1805499).sum := by decide
  have hdescent : baseEnd_1805499 < baseStart_1805499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805503 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 3, 2, 2]
def baseStart_1805503 : Nat := 118140960795 + 1805503 * 2 ^ 59
def prefixEnd_1805503 : Nat := 4983230072969 + 3 ^ 40 * 1805503 * 2
def baseEnd_1805503 : Nat := 927090862134754694909149

theorem tailTrace_1805503 : CollatzResearch.WordTrace tailWord_1805503 prefixEnd_1805503 927090862134754694909149 := by
  unfold tailWord_1805503
  simp only [CollatzResearch.WordTrace]
  refine ⟨65852104377978461208085163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43901402918652307472056775 65852104377978461208085163)
  ·
    refine ⟨98778156566967691812127745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65852104377978461208085163 98778156566967691812127745)
    ·
      refine ⟨74083617425225768859095809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98778156566967691812127745 74083617425225768859095809)
      ·
        refine ⟨55562713068919326644321857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74083617425225768859095809 55562713068919326644321857)
        ·
          refine ⟨41672034801689494983241393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55562713068919326644321857 41672034801689494983241393)
          ·
            refine ⟨31254026101267121237431045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41672034801689494983241393 31254026101267121237431045)
            ·
              refine ⟨5860129893987585232018321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31254026101267121237431045 5860129893987585232018321)
              ·
                refine ⟨4395097420490688924013741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5860129893987585232018321 4395097420490688924013741)
                ·
                  refine ⟨1648161532684008346505153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4395097420490688924013741 1648161532684008346505153)
                  ·
                    refine ⟨1236121149513006259878865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1648161532684008346505153 1236121149513006259878865)
                    ·
                      refine ⟨927090862134754694909149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1236121149513006259878865 927090862134754694909149)
                      ·
                        rfl

theorem cell23_1805503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_1805503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805503 prefixEnd_1805503 := by exact prefixLift 1805503
  have htrace : WordTrace (prefixWord ++ tailWord_1805503) baseStart_1805503 baseEnd_1805503 := by
    simpa [prefixWord, tailWord_1805503, baseEnd_1805503] using wordTrace_append hprefix tailTrace_1805503
  have hstable : (prefixWord ++ tailWord_1805503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805503).length < 2 ^ (prefixWord ++ tailWord_1805503).sum := by decide
  have hdescent : baseEnd_1805503 < baseStart_1805503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805559 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_1805559 : Nat := 118140960795 + 1805559 * 2 ^ 59
def prefixEnd_1805559 : Nat := 4983230072969 + 3 ^ 40 * 1805559 * 2
def baseEnd_1805559 : Nat := 927119617051406475808891

theorem tailTrace_1805559 : CollatzResearch.WordTrace tailWord_1805559 prefixEnd_1805559 927119617051406475808891 := by
  unfold tailWord_1805559
  simp only [CollatzResearch.WordTrace]
  refine ⟨65854146865775582772123731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43902764577183721848082487 65854146865775582772123731)
  ·
    refine ⟨98781220298663374158185597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65854146865775582772123731 98781220298663374158185597)
    ·
      refine ⟨37042957611998765309319599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98781220298663374158185597 37042957611998765309319599)
      ·
        refine ⟨55564436417998147963979399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37042957611998765309319599 55564436417998147963979399)
        ·
          refine ⟨83346654626997221945969099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55564436417998147963979399 83346654626997221945969099)
          ·
            refine ⟨125019981940495832918953649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83346654626997221945969099 125019981940495832918953649)
            ·
              refine ⟨93764986455371874689215237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125019981940495832918953649 93764986455371874689215237)
              ·
                refine ⟨17580934960382226504227857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93764986455371874689215237 17580934960382226504227857)
                ·
                  refine ⟨13185701220286669878170893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17580934960382226504227857 13185701220286669878170893)
                  ·
                    refine ⟨4944637957607501204314085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13185701220286669878170893 4944637957607501204314085)
                    ·
                      refine ⟨927119617051406475808891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4944637957607501204314085 927119617051406475808891)
                      ·
                        rfl

theorem cell23_1805559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_1805559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805559 prefixEnd_1805559 := by exact prefixLift 1805559
  have htrace : WordTrace (prefixWord ++ tailWord_1805559) baseStart_1805559 baseEnd_1805559 := by
    simpa [prefixWord, tailWord_1805559, baseEnd_1805559] using wordTrace_append hprefix tailTrace_1805559
  have hstable : (prefixWord ++ tailWord_1805559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805559).length < 2 ^ (prefixWord ++ tailWord_1805559).sum := by decide
  have hdescent : baseEnd_1805559 < baseStart_1805559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805570 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1805570 : Nat := 118140960795 + 1805570 * 2 ^ 59
def prefixEnd_1805570 : Nat := 4983230072969 + 3 ^ 40 * 1805570 * 2
def baseEnd_1805570 : Nat := 927125265338605932771341

theorem tailTrace_1805570 : CollatzResearch.WordTrace tailWord_1805570 prefixEnd_1805570 927125265338605932771341 := by
  unfold tailWord_1805570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16463637017183932912693541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43903032045823821100516109 16463637017183932912693541)
  ·
    refine ⟨3086931940721987421130039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16463637017183932912693541 3086931940721987421130039)
    ·
      refine ⟨4630397911082981131695059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3086931940721987421130039 4630397911082981131695059)
      ·
        refine ⟨6945596866624471697542589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4630397911082981131695059 6945596866624471697542589)
        ·
          refine ⟨2604598824984176886578471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6945596866624471697542589 2604598824984176886578471)
          ·
            refine ⟨3906898237476265329867707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604598824984176886578471 3906898237476265329867707)
            ·
              refine ⟨5860347356214397994801561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906898237476265329867707 5860347356214397994801561)
              ·
                refine ⟨4395260517160798496101171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5860347356214397994801561 4395260517160798496101171)
                ·
                  refine ⟨6592890775741197744151757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395260517160798496101171 6592890775741197744151757)
                  ·
                    refine ⟨2472334040902949154056909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6592890775741197744151757 2472334040902949154056909)
                    ·
                      refine ⟨927125265338605932771341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2472334040902949154056909 927125265338605932771341)
                      ·
                        rfl

theorem cell23_1805570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1805570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805570 prefixEnd_1805570 := by exact prefixLift 1805570
  have htrace : WordTrace (prefixWord ++ tailWord_1805570) baseStart_1805570 baseEnd_1805570 := by
    simpa [prefixWord, tailWord_1805570, baseEnd_1805570] using wordTrace_append hprefix tailTrace_1805570
  have hstable : (prefixWord ++ tailWord_1805570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805570).length < 2 ^ (prefixWord ++ tailWord_1805570).sum := by decide
  have hdescent : baseEnd_1805570 < baseStart_1805570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805589 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1805589 : Nat := 118140960795 + 1805589 * 2 ^ 59
def prefixEnd_1805589 : Nat := 4983230072969 + 3 ^ 40 * 1805589 * 2
def baseEnd_1805589 : Nat := 927135021471041358433753

theorem tailTrace_1805589 : CollatzResearch.WordTrace tailWord_1805589 prefixEnd_1805589 927135021471041358433753 := by
  unfold tailWord_1805589
  simp only [CollatzResearch.WordTrace]
  refine ⟨65855241055666897895715821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43903494037111265263810547 65855241055666897895715821)
  ·
    refine ⟨24695715395875086710893433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65855241055666897895715821 24695715395875086710893433)
    ·
      refine ⟨18521786546906315033170075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24695715395875086710893433 18521786546906315033170075)
      ·
        refine ⟨27782679820359472549755113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18521786546906315033170075 27782679820359472549755113)
        ·
          refine ⟨20837009865269604412316335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27782679820359472549755113 20837009865269604412316335)
          ·
            refine ⟨31255514797904406618474503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20837009865269604412316335 31255514797904406618474503)
            ·
              refine ⟨46883272196856609927711755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31255514797904406618474503 46883272196856609927711755)
              ·
                refine ⟨70324908295284914891567633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46883272196856609927711755 70324908295284914891567633)
                ·
                  refine ⟨52743681221463686168675725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70324908295284914891567633 52743681221463686168675725)
                  ·
                    refine ⟨19778880458048882313253397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52743681221463686168675725 19778880458048882313253397)
                    ·
                      refine ⟨927135021471041358433753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19778880458048882313253397 927135021471041358433753)
                      ·
                        rfl

theorem cell23_1805589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1805589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805589 prefixEnd_1805589 := by exact prefixLift 1805589
  have htrace : WordTrace (prefixWord ++ tailWord_1805589) baseStart_1805589 baseEnd_1805589 := by
    simpa [prefixWord, tailWord_1805589, baseEnd_1805589] using wordTrace_append hprefix tailTrace_1805589
  have hstable : (prefixWord ++ tailWord_1805589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805589).length < 2 ^ (prefixWord ++ tailWord_1805589).sum := by decide
  have hdescent : baseEnd_1805589 < baseStart_1805589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805596 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1805596 : Nat := 118140960795 + 1805596 * 2 ^ 59
def prefixEnd_1805596 : Nat := 4983230072969 + 3 ^ 40 * 1805596 * 2
def baseEnd_1805596 : Nat := 927138615835622831046221

theorem tailTrace_1805596 : CollatzResearch.WordTrace tailWord_1805596 prefixEnd_1805596 927138615835622831046221 := by
  unfold tailWord_1805596
  simp only [CollatzResearch.WordTrace]
  refine ⟨32927748183320769045610321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43903664244427692060813761 32927748183320769045610321)
  ·
    refine ⟨24695811137490576784207741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32927748183320769045610321 24695811137490576784207741)
    ·
      refine ⟨9260929176558966294077903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24695811137490576784207741 9260929176558966294077903)
      ·
        refine ⟨13891393764838449441116855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9260929176558966294077903 13891393764838449441116855)
        ·
          refine ⟨20837090647257674161675283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13891393764838449441116855 20837090647257674161675283)
          ·
            refine ⟨31255635970886511242512925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20837090647257674161675283 31255635970886511242512925)
            ·
              refine ⟨11720863489082441715942347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31255635970886511242512925 11720863489082441715942347)
              ·
                refine ⟨17581295233623662573913521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11720863489082441715942347 17581295233623662573913521)
                ·
                  refine ⟨13185971425217746930435141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17581295233623662573913521 13185971425217746930435141)
                  ·
                    refine ⟨2472369642228327549456589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13185971425217746930435141 2472369642228327549456589)
                    ·
                      refine ⟨927138615835622831046221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2472369642228327549456589 927138615835622831046221)
                      ·
                        rfl

theorem cell23_1805596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1805596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805596 prefixEnd_1805596 := by exact prefixLift 1805596
  have htrace : WordTrace (prefixWord ++ tailWord_1805596) baseStart_1805596 baseEnd_1805596 := by
    simpa [prefixWord, tailWord_1805596, baseEnd_1805596] using wordTrace_append hprefix tailTrace_1805596
  have hstable : (prefixWord ++ tailWord_1805596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805596).length < 2 ^ (prefixWord ++ tailWord_1805596).sum := by decide
  have hdescent : baseEnd_1805596 < baseStart_1805596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805610 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1805610 : Nat := 118140960795 + 1805610 * 2 ^ 59
def prefixEnd_1805610 : Nat := 4983230072969 + 3 ^ 40 * 1805610 * 2
def baseEnd_1805610 : Nat := 927145804564785776271157

theorem tailTrace_1805610 : CollatzResearch.WordTrace tailWord_1805610 prefixEnd_1805610 927145804564785776271157 := by
  unfold tailWord_1805610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464001747147704620557571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43904004659060545654820189 16464001747147704620557571)
  ·
    refine ⟨24696002620721556930836357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16464001747147704620557571 24696002620721556930836357)
    ·
      refine ⟨4630500491385291924531817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24696002620721556930836357 4630500491385291924531817)
      ·
        refine ⟨3472875368538968943398863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4630500491385291924531817 3472875368538968943398863)
        ·
          refine ⟨5209313052808453415098295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472875368538968943398863 5209313052808453415098295)
          ·
            refine ⟨7813969579212680122647443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209313052808453415098295 7813969579212680122647443)
            ·
              refine ⟨11720954368819020183971165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7813969579212680122647443 11720954368819020183971165)
              ·
                refine ⟨4395357888307132568989187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11720954368819020183971165 4395357888307132568989187)
                ·
                  refine ⟨6593036832460698853483781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395357888307132568989187 6593036832460698853483781)
                  ·
                    refine ⟨1236194406086381035028209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6593036832460698853483781 1236194406086381035028209)
                    ·
                      refine ⟨927145804564785776271157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1236194406086381035028209 927145804564785776271157)
                      ·
                        rfl

theorem cell23_1805610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1805610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805610 prefixEnd_1805610 := by exact prefixLift 1805610
  have htrace : WordTrace (prefixWord ++ tailWord_1805610) baseStart_1805610 baseEnd_1805610 := by
    simpa [prefixWord, tailWord_1805610, baseEnd_1805610] using wordTrace_append hprefix tailTrace_1805610
  have hstable : (prefixWord ++ tailWord_1805610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805610).length < 2 ^ (prefixWord ++ tailWord_1805610).sum := by decide
  have hdescent : baseEnd_1805610 < baseStart_1805610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805626 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_1805626 : Nat := 118140960795 + 1805626 * 2 ^ 59
def prefixEnd_1805626 : Nat := 4983230072969 + 3 ^ 40 * 1805626 * 2
def baseEnd_1805626 : Nat := 927154020255257713671083

theorem tailTrace_1805626 : CollatzResearch.WordTrace tailWord_1805626 prefixEnd_1805626 927154020255257713671083 := by
  unfold tailWord_1805626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464147639133213303703183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43904393704355235476541821 16464147639133213303703183)
  ·
    refine ⟨24696221458699819955554775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16464147639133213303703183 24696221458699819955554775)
    ·
      refine ⟨37044332188049729933332163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24696221458699819955554775 37044332188049729933332163)
      ·
        refine ⟨55566498282074594899998245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37044332188049729933332163 55566498282074594899998245)
        ·
          refine ⟨10418718427888986543749671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55566498282074594899998245 10418718427888986543749671)
          ·
            refine ⟨15628077641833479815624507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10418718427888986543749671 15628077641833479815624507)
            ·
              refine ⟨23442116462750219723436761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15628077641833479815624507 23442116462750219723436761)
              ·
                refine ⟨17581587347062664792577571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23442116462750219723436761 17581587347062664792577571)
                ·
                  refine ⟨26372381020593997188866357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17581587347062664792577571 26372381020593997188866357)
                  ·
                    refine ⟨2472410720680687236456221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26372381020593997188866357 2472410720680687236456221)
                    ·
                      refine ⟨927154020255257713671083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2472410720680687236456221 927154020255257713671083)
                      ·
                        rfl

theorem cell23_1805626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_1805626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805626 prefixEnd_1805626 := by exact prefixLift 1805626
  have htrace : WordTrace (prefixWord ++ tailWord_1805626) baseStart_1805626 baseEnd_1805626 := by
    simpa [prefixWord, tailWord_1805626, baseEnd_1805626] using wordTrace_append hprefix tailTrace_1805626
  have hstable : (prefixWord ++ tailWord_1805626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805626).length < 2 ^ (prefixWord ++ tailWord_1805626).sum := by decide
  have hdescent : baseEnd_1805626 < baseStart_1805626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805638 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1805638 : Nat := 118140960795 + 1805638 * 2 ^ 59
def prefixEnd_1805638 : Nat := 4983230072969 + 3 ^ 40 * 1805638 * 2
def baseEnd_1805638 : Nat := 927160182023111666721029

theorem tailTrace_1805638 : CollatzResearch.WordTrace tailWord_1805638 prefixEnd_1805638 927160182023111666721029 := by
  unfold tailWord_1805638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2058032132265293102007799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43904685488326252842833045 2058032132265293102007799)
  ·
    refine ⟨3087048198397939653011699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2058032132265293102007799 3087048198397939653011699)
    ·
      refine ⟨4630572297596909479517549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3087048198397939653011699 4630572297596909479517549)
      ·
        refine ⟨1736464611598841054819081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4630572297596909479517549 1736464611598841054819081)
        ·
          refine ⟨1302348458699130791114311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1736464611598841054819081 1302348458699130791114311)
          ·
            refine ⟨1953522688048696186671467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302348458699130791114311 1953522688048696186671467)
            ·
              refine ⟨2930284032073044280007201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953522688048696186671467 2930284032073044280007201)
              ·
                refine ⟨2197713024054783210005401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930284032073044280007201 2197713024054783210005401)
                ·
                  refine ⟨1648284768041087407504051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2197713024054783210005401 1648284768041087407504051)
                  ·
                    refine ⟨2472427152061631111256077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1648284768041087407504051 2472427152061631111256077)
                    ·
                      refine ⟨927160182023111666721029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2472427152061631111256077 927160182023111666721029)
                      ·
                        rfl

theorem cell23_1805638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1805638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805638 prefixEnd_1805638 := by exact prefixLift 1805638
  have htrace : WordTrace (prefixWord ++ tailWord_1805638) baseStart_1805638 baseEnd_1805638 := by
    simpa [prefixWord, tailWord_1805638, baseEnd_1805638] using wordTrace_append hprefix tailTrace_1805638
  have hstable : (prefixWord ++ tailWord_1805638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805638).length < 2 ^ (prefixWord ++ tailWord_1805638).sum := by decide
  have hdescent : baseEnd_1805638 < baseStart_1805638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805646 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_1805646 : Nat := 118140960795 + 1805646 * 2 ^ 59
def prefixEnd_1805646 : Nat := 4983230072969 + 3 ^ 40 * 1805646 * 2
def baseEnd_1805646 : Nat := 309054763289449211806997

theorem tailTrace_1805646 : CollatzResearch.WordTrace tailWord_1805646 prefixEnd_1805646 309054763289449211806997 := by
  unfold tailWord_1805646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8232165002057549578817599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43904880010973597753693861 8232165002057549578817599)
  ·
    refine ⟨12348247503086324368226399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8232165002057549578817599 12348247503086324368226399)
    ·
      refine ⟨18522371254629486552339599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12348247503086324368226399 18522371254629486552339599)
      ·
        refine ⟨27783556881944229828509399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18522371254629486552339599 27783556881944229828509399)
        ·
          refine ⟨41675335322916344742764099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27783556881944229828509399 41675335322916344742764099)
          ·
            refine ⟨62513002984374517114146149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41675335322916344742764099 62513002984374517114146149)
            ·
              refine ⟨11721188059570221958902403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62513002984374517114146149 11721188059570221958902403)
              ·
                refine ⟨17581782089355332938353605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11721188059570221958902403 17581782089355332938353605)
                ·
                  refine ⟨3296584141754124925941301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17581782089355332938353605 3296584141754124925941301)
                  ·
                    refine ⟨309054763289449211806997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3296584141754124925941301 309054763289449211806997)
                    ·
                      rfl

theorem cell23_1805646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_1805646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805646 prefixEnd_1805646 := by exact prefixLift 1805646
  have htrace : WordTrace (prefixWord ++ tailWord_1805646) baseStart_1805646 baseEnd_1805646 := by
    simpa [prefixWord, tailWord_1805646, baseEnd_1805646] using wordTrace_append hprefix tailTrace_1805646
  have hstable : (prefixWord ++ tailWord_1805646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805646).length < 2 ^ (prefixWord ++ tailWord_1805646).sum := by decide
  have hdescent : baseEnd_1805646 < baseStart_1805646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805661 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1805661 : Nat := 118140960795 + 1805661 * 2 ^ 59
def prefixEnd_1805661 : Nat := 4983230072969 + 3 ^ 40 * 1805661 * 2
def baseEnd_1805661 : Nat := 927171992078165076733423

theorem tailTrace_1805661 : CollatzResearch.WordTrace tailWord_1805661 prefixEnd_1805661 927171992078165076733423 := by
  unfold tailWord_1805661
  simp only [CollatzResearch.WordTrace]
  refine ⟨65857867111406054192336837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43905244740937369461557891 65857867111406054192336837)
  ·
    refine ⟨12348350083388635161063157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65857867111406054192336837 12348350083388635161063157)
    ·
      refine ⟨1157657820317684546349671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12348350083388635161063157 1157657820317684546349671)
      ·
        refine ⟨1736486730476526819524507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1157657820317684546349671 1736486730476526819524507)
        ·
          refine ⟨2604730095714790229286761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736486730476526819524507 2604730095714790229286761)
          ·
            refine ⟨1953547571786092671965071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2604730095714790229286761 1953547571786092671965071)
            ·
              refine ⟨2930321357679139007947607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953547571786092671965071 2930321357679139007947607)
              ·
                refine ⟨4395482036518708511921411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930321357679139007947607 4395482036518708511921411)
                ·
                  refine ⟨6593223054778062767882117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395482036518708511921411 6593223054778062767882117)
                  ·
                    refine ⟨1236229322770886768977897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6593223054778062767882117 1236229322770886768977897)
                    ·
                      refine ⟨927171992078165076733423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1236229322770886768977897 927171992078165076733423)
                      ·
                        rfl

theorem cell23_1805661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1805661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805661 prefixEnd_1805661 := by exact prefixLift 1805661
  have htrace : WordTrace (prefixWord ++ tailWord_1805661) baseStart_1805661 baseEnd_1805661 := by
    simpa [prefixWord, tailWord_1805661, baseEnd_1805661] using wordTrace_append hprefix tailTrace_1805661
  have hstable : (prefixWord ++ tailWord_1805661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805661).length < 2 ^ (prefixWord ++ tailWord_1805661).sum := by decide
  have hdescent : baseEnd_1805661 < baseStart_1805661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805703 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_1805703 : Nat := 118140960795 + 1805703 * 2 ^ 59
def prefixEnd_1805703 : Nat := 4983230072969 + 3 ^ 40 * 1805703 * 2
def baseEnd_1805703 : Nat := 927193558265653912408229

theorem tailTrace_1805703 : CollatzResearch.WordTrace tailWord_1805703 prefixEnd_1805703 927193558265653912408229 := by
  unfold tailWord_1805703
  simp only [CollatzResearch.WordTrace]
  refine ⟨65859398977253895365365763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43906265984835930243577175 65859398977253895365365763)
  ·
    refine ⟨98789098465880843048048645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65859398977253895365365763 98789098465880843048048645)
    ·
      refine ⟨18522955962352658071509121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98789098465880843048048645 18522955962352658071509121)
      ·
        refine ⟨13892216971764493553631841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18522955962352658071509121 13892216971764493553631841)
        ·
          refine ⟨10419162728823370165223881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13892216971764493553631841 10419162728823370165223881)
          ·
            refine ⟨7814372046617527623917911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10419162728823370165223881 7814372046617527623917911)
            ·
              refine ⟨11721558069926291435876867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814372046617527623917911 11721558069926291435876867)
              ·
                refine ⟨17582337104889437153815301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11721558069926291435876867 17582337104889437153815301)
                ·
                  refine ⟨3296688207166769466340369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17582337104889437153815301 3296688207166769466340369)
                  ·
                    refine ⟨2472516155375077099755277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3296688207166769466340369 2472516155375077099755277)
                    ·
                      refine ⟨927193558265653912408229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2472516155375077099755277 927193558265653912408229)
                      ·
                        rfl

theorem cell23_1805703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_1805703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805703 prefixEnd_1805703 := by exact prefixLift 1805703
  have htrace : WordTrace (prefixWord ++ tailWord_1805703) baseStart_1805703 baseEnd_1805703 := by
    simpa [prefixWord, tailWord_1805703, baseEnd_1805703] using wordTrace_append hprefix tailTrace_1805703
  have hstable : (prefixWord ++ tailWord_1805703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805703).length < 2 ^ (prefixWord ++ tailWord_1805703).sum := by decide
  have hdescent : baseEnd_1805703 < baseStart_1805703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805743 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 1, 5, 2]
def baseStart_1805743 : Nat := 118140960795 + 1805743 * 2 ^ 59
def prefixEnd_1805743 : Nat := 4983230072969 + 3 ^ 40 * 1805743 * 2
def baseEnd_1805743 : Nat := 927214097491833755908045

theorem tailTrace_1805743 : CollatzResearch.WordTrace tailWord_1805743 prefixEnd_1805743 927214097491833755908045 := by
  unfold tailWord_1805743
  simp only [CollatzResearch.WordTrace]
  refine ⟨65860857897108982196821883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43907238598072654797881255 65860857897108982196821883)
  ·
    refine ⟨98791286845663473295232825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65860857897108982196821883 98791286845663473295232825)
    ·
      refine ⟨74093465134247604971424619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98791286845663473295232825 74093465134247604971424619)
      ·
        refine ⟨111140197701371407457136929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74093465134247604971424619 111140197701371407457136929)
        ·
          refine ⟨83355148276028555592852697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111140197701371407457136929 83355148276028555592852697)
          ·
            refine ⟨62516361207021416694639523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83355148276028555592852697 62516361207021416694639523)
            ·
              refine ⟨93774541810532125041959285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62516361207021416694639523 93774541810532125041959285)
              ·
                refine ⟨8791363294737386722683683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93774541810532125041959285 8791363294737386722683683)
                ·
                  refine ⟨13187044942106080084025525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8791363294737386722683683 13187044942106080084025525)
                  ·
                    refine ⟨1236285463322445007877393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13187044942106080084025525 1236285463322445007877393)
                    ·
                      refine ⟨927214097491833755908045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1236285463322445007877393 927214097491833755908045)
                      ·
                        rfl

theorem cell23_1805743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 5, 2].length) (baseStart_1805743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805743 prefixEnd_1805743 := by exact prefixLift 1805743
  have htrace : WordTrace (prefixWord ++ tailWord_1805743) baseStart_1805743 baseEnd_1805743 := by
    simpa [prefixWord, tailWord_1805743, baseEnd_1805743] using wordTrace_append hprefix tailTrace_1805743
  have hstable : (prefixWord ++ tailWord_1805743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805743).length < 2 ^ (prefixWord ++ tailWord_1805743).sum := by decide
  have hdescent : baseEnd_1805743 < baseStart_1805743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805746 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1805746 : Nat := 118140960795 + 1805746 * 2 ^ 59
def prefixEnd_1805746 : Nat := 4983230072969 + 3 ^ 40 * 1805746 * 2
def baseEnd_1805746 : Nat := 927215637933797244170531

theorem tailTrace_1805746 : CollatzResearch.WordTrace tailWord_1805746 prefixEnd_1805746 927215637933797244170531 := by
  unfold tailWord_1805746
  simp only [CollatzResearch.WordTrace]
  refine ⟨16465241829024528427295273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43907311544065409139454061 16465241829024528427295273)
  ·
    refine ⟨12348931371768396320471455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16465241829024528427295273 12348931371768396320471455)
    ·
      refine ⟨18523397057652594480707183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12348931371768396320471455 18523397057652594480707183)
      ·
        refine ⟨27785095586478891721060775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18523397057652594480707183 27785095586478891721060775)
        ·
          refine ⟨41677643379718337581591163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27785095586478891721060775 41677643379718337581591163)
          ·
            refine ⟨62516465069577506372386745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41677643379718337581591163 62516465069577506372386745)
            ·
              refine ⟨46887348802183129779290059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62516465069577506372386745 46887348802183129779290059)
              ·
                refine ⟨70331023203274694668935089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46887348802183129779290059 70331023203274694668935089)
                ·
                  refine ⟨52748267402456021001701317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70331023203274694668935089 52748267402456021001701317)
                  ·
                    refine ⟨9890300137960503937818997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52748267402456021001701317 9890300137960503937818997)
                    ·
                      refine ⟨927215637933797244170531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9890300137960503937818997 927215637933797244170531)
                      ·
                        rfl

theorem cell23_1805746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1805746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805746 prefixEnd_1805746 := by exact prefixLift 1805746
  have htrace : WordTrace (prefixWord ++ tailWord_1805746) baseStart_1805746 baseEnd_1805746 := by
    simpa [prefixWord, tailWord_1805746, baseEnd_1805746] using wordTrace_append hprefix tailTrace_1805746
  have hstable : (prefixWord ++ tailWord_1805746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805746).length < 2 ^ (prefixWord ++ tailWord_1805746).sum := by decide
  have hdescent : baseEnd_1805746 < baseStart_1805746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805760 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 2, 3, 2]
def baseStart_1805760 : Nat := 118140960795 + 1805760 * 2 ^ 59
def prefixEnd_1805760 : Nat := 4983230072969 + 3 ^ 40 * 1805760 * 2
def baseEnd_1805760 : Nat := 927222826662960189395467

theorem tailTrace_1805760 : CollatzResearch.WordTrace tailWord_1805760 prefixEnd_1805760 927222826662960189395467 := by
  unfold tailWord_1805760
  simp only [CollatzResearch.WordTrace]
  refine ⟨32930738969023697050095367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43907651958698262733460489 32930738969023697050095367)
  ·
    refine ⟨49396108453535545575143051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32930738969023697050095367 49396108453535545575143051)
    ·
      refine ⟨74094162680303318362714577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49396108453535545575143051 74094162680303318362714577)
      ·
        refine ⟨55570622010227488772035933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74094162680303318362714577 55570622010227488772035933)
        ·
          refine ⟨20838983253835308289513475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55570622010227488772035933 20838983253835308289513475)
          ·
            refine ⟨31258474880752962434270213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20838983253835308289513475 31258474880752962434270213)
            ·
              refine ⟨5860964040141180456425665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31258474880752962434270213 5860964040141180456425665)
              ·
                refine ⟨4395723030105885342319249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5860964040141180456425665 4395723030105885342319249)
                ·
                  refine ⟨3296792272579414006739437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4395723030105885342319249 3296792272579414006739437)
                  ·
                    refine ⟨1236297102217280252527289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296792272579414006739437 1236297102217280252527289)
                    ·
                      refine ⟨927222826662960189395467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1236297102217280252527289 927222826662960189395467)
                      ·
                        rfl

theorem cell23_1805760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_1805760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805760 prefixEnd_1805760 := by exact prefixLift 1805760
  have htrace : WordTrace (prefixWord ++ tailWord_1805760) baseStart_1805760 baseEnd_1805760 := by
    simpa [prefixWord, tailWord_1805760, baseEnd_1805760] using wordTrace_append hprefix tailTrace_1805760
  have hstable : (prefixWord ++ tailWord_1805760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805760).length < 2 ^ (prefixWord ++ tailWord_1805760).sum := by decide
  have hdescent : baseEnd_1805760 < baseStart_1805760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805767 : List Nat := [1, 1, 4, 1, 1, 3, 3, 4, 1, 1, 3]
def baseStart_1805767 : Nat := 118140960795 + 1805767 * 2 ^ 59
def prefixEnd_1805767 : Nat := 4983230072969 + 3 ^ 40 * 1805767 * 2
def baseEnd_1805767 : Nat := 927226421027541662007935

theorem tailTrace_1805767 : CollatzResearch.WordTrace tailWord_1805767 prefixEnd_1805767 927226421027541662007935 := by
  unfold tailWord_1805767
  simp only [CollatzResearch.WordTrace]
  refine ⟨65861733249022034295695555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43907822166014689530463703 65861733249022034295695555)
  ·
    refine ⟨98792599873533051443543333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65861733249022034295695555 98792599873533051443543333)
    ·
      refine ⟨18523612476287447145664375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98792599873533051443543333 18523612476287447145664375)
      ·
        refine ⟨27785418714431170718496563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18523612476287447145664375 27785418714431170718496563)
        ·
          refine ⟨41678128071646756077744845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27785418714431170718496563 41678128071646756077744845)
          ·
            refine ⟨15629298026867533529154317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41678128071646756077744845 15629298026867533529154317)
            ·
              refine ⟨5860986760075325073432869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15629298026867533529154317 5860986760075325073432869)
              ·
                refine ⟨1098935017514123451268663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5860986760075325073432869 1098935017514123451268663)
                ·
                  refine ⟨1648402526271185176902995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098935017514123451268663 1648402526271185176902995)
                  ·
                    refine ⟨2472603789406777765354493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1648402526271185176902995 2472603789406777765354493)
                    ·
                      refine ⟨927226421027541662007935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2472603789406777765354493 927226421027541662007935)
                      ·
                        rfl

theorem cell23_1805767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_1805767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805767 prefixEnd_1805767 := by exact prefixLift 1805767
  have htrace : WordTrace (prefixWord ++ tailWord_1805767) baseStart_1805767 baseEnd_1805767 := by
    simpa [prefixWord, tailWord_1805767, baseEnd_1805767] using wordTrace_append hprefix tailTrace_1805767
  have hstable : (prefixWord ++ tailWord_1805767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805767).length < 2 ^ (prefixWord ++ tailWord_1805767).sum := by decide
  have hdescent : baseEnd_1805767 < baseStart_1805767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805796 : List Nat := [2, 3, 1, 1, 1, 1, 1, 13]
def baseStart_1805796 : Nat := 118140960795 + 1805796 * 2 ^ 59
def prefixEnd_1805796 : Nat := 4983230072969 + 3 ^ 40 * 1805796 * 2
def baseEnd_1805796 : Nat := 34342270813574890686863

theorem tailTrace_1805796 : CollatzResearch.WordTrace tailWord_1805796 prefixEnd_1805796 34342270813574890686863 := by
  unfold tailWord_1805796
  simp only [CollatzResearch.WordTrace]
  refine ⟨32931395482958486124250621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43908527310611314832334161 32931395482958486124250621)
  ·
    refine ⟨12349273306109432296593983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32931395482958486124250621 12349273306109432296593983)
    ·
      refine ⟨18523909959164148444890975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12349273306109432296593983 18523909959164148444890975)
      ·
        refine ⟨27785864938746222667336463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18523909959164148444890975 27785864938746222667336463)
        ·
          refine ⟨41678797408119334001004695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27785864938746222667336463 41678797408119334001004695)
          ·
            refine ⟨62518196112179001001507043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41678797408119334001004695 62518196112179001001507043)
            ·
              refine ⟨93777294168268501502260565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62518196112179001001507043 93777294168268501502260565)
              ·
                refine ⟨34342270813574890686863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 93777294168268501502260565 34342270813574890686863)
                ·
                  rfl

theorem cell23_1805796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 13].length) (baseStart_1805796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805796 prefixEnd_1805796 := by exact prefixLift 1805796
  have htrace : WordTrace (prefixWord ++ tailWord_1805796) baseStart_1805796 baseEnd_1805796 := by
    simpa [prefixWord, tailWord_1805796, baseEnd_1805796] using wordTrace_append hprefix tailTrace_1805796
  have hstable : (prefixWord ++ tailWord_1805796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805796).length < 2 ^ (prefixWord ++ tailWord_1805796).sum := by decide
  have hdescent : baseEnd_1805796 < baseStart_1805796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805853 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1805853 : Nat := 118140960795 + 1805853 * 2 ^ 59
def prefixEnd_1805853 : Nat := 4983230072969 + 3 ^ 40 * 1805853 * 2
def baseEnd_1805853 : Nat := 927270580363828325532539

theorem tailTrace_1805853 : CollatzResearch.WordTrace tailWord_1805853 prefixEnd_1805853 927270580363828325532539 := by
  unfold tailWord_1805853
  simp only [CollatzResearch.WordTrace]
  refine ⟨65864869926710470983326213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43909913284473647322217475 65864869926710470983326213)
  ·
    refine ⟨12349663111258213309373665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65864869926710470983326213 12349663111258213309373665)
    ·
      refine ⟨9262247333443659982030249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12349663111258213309373665 9262247333443659982030249)
      ·
        refine ⟨6946685500082744986522687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9262247333443659982030249 6946685500082744986522687)
        ·
          refine ⟨10420028250124117479784031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6946685500082744986522687 10420028250124117479784031)
          ·
            refine ⟨15630042375186176219676047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10420028250124117479784031 15630042375186176219676047)
            ·
              refine ⟨23445063562779264329514071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15630042375186176219676047 23445063562779264329514071)
              ·
                refine ⟨35167595344168896494271107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23445063562779264329514071 35167595344168896494271107)
                ·
                  refine ⟨52751393016253344741406661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35167595344168896494271107 52751393016253344741406661)
                  ·
                    refine ⟨9890886190547502139013749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52751393016253344741406661 9890886190547502139013749)
                    ·
                      refine ⟨927270580363828325532539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9890886190547502139013749 927270580363828325532539)
                      ·
                        rfl

theorem cell23_1805853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1805853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805853 prefixEnd_1805853 := by exact prefixLift 1805853
  have htrace : WordTrace (prefixWord ++ tailWord_1805853) baseStart_1805853 baseEnd_1805853 := by
    simpa [prefixWord, tailWord_1805853, baseEnd_1805853] using wordTrace_append hprefix tailTrace_1805853
  have hstable : (prefixWord ++ tailWord_1805853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805853).length < 2 ^ (prefixWord ++ tailWord_1805853).sum := by decide
  have hdescent : baseEnd_1805853 < baseStart_1805853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805893 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_1805893 : Nat := 118140960795 + 1805893 * 2 ^ 59
def prefixEnd_1805893 : Nat := 4983230072969 + 3 ^ 40 * 1805893 * 2
def baseEnd_1805893 : Nat := 927291119590008169032355

theorem tailTrace_1805893 : CollatzResearch.WordTrace tailWord_1805893 prefixEnd_1805893 927291119590008169032355 := by
  unfold tailWord_1805893
  simp only [CollatzResearch.WordTrace]
  refine ⟨65866328846565557814782333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43910885897710371876521555 65866328846565557814782333)
  ·
    refine ⟨24699873317462084180543375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65866328846565557814782333 24699873317462084180543375)
    ·
      refine ⟨37049809976193126270815063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24699873317462084180543375 37049809976193126270815063)
      ·
        refine ⟨55574714964289689406222595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37049809976193126270815063 55574714964289689406222595)
        ·
          refine ⟨83362072446434534109333893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55574714964289689406222595 83362072446434534109333893)
          ·
            refine ⟨15630388583706475145500105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83362072446434534109333893 15630388583706475145500105)
            ·
              refine ⟨11722791437779856359125079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15630388583706475145500105 11722791437779856359125079)
              ·
                refine ⟨17584187156669784538687619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11722791437779856359125079 17584187156669784538687619)
                ·
                  refine ⟨26376280735004676808031429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17584187156669784538687619 26376280735004676808031429)
                  ·
                    refine ⟨4945552637813376901505893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26376280735004676808031429 4945552637813376901505893)
                    ·
                      refine ⟨927291119590008169032355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4945552637813376901505893 927291119590008169032355)
                      ·
                        rfl

theorem cell23_1805893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_1805893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805893 prefixEnd_1805893 := by exact prefixLift 1805893
  have htrace : WordTrace (prefixWord ++ tailWord_1805893) baseStart_1805893 baseEnd_1805893 := by
    simpa [prefixWord, tailWord_1805893, baseEnd_1805893] using wordTrace_append hprefix tailTrace_1805893
  have hstable : (prefixWord ++ tailWord_1805893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805893).length < 2 ^ (prefixWord ++ tailWord_1805893).sum := by decide
  have hdescent : baseEnd_1805893 < baseStart_1805893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805920 : List Nat := [2, 1, 1, 3, 2, 1, 1, 7, 5]
def baseStart_1805920 : Nat := 118140960795 + 1805920 * 2 ^ 59
def prefixEnd_1805920 : Nat := 4983230072969 + 3 ^ 40 * 1805920 * 2
def baseEnd_1805920 : Nat := 103033887063075507043859

theorem tailTrace_1805920 : CollatzResearch.WordTrace tailWord_1805920 prefixEnd_1805920 103033887063075507043859 := by
  unfold tailWord_1805920
  simp only [CollatzResearch.WordTrace]
  refine ⟨32933656808733870713007607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43911542411645160950676809 32933656808733870713007607)
  ·
    refine ⟨49400485213100806069511411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32933656808733870713007607 49400485213100806069511411)
    ·
      refine ⟨74100727819651209104267117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49400485213100806069511411 74100727819651209104267117)
      ·
        refine ⟨27787772932369203414100169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74100727819651209104267117 27787772932369203414100169)
        ·
          refine ⟨20840829699276902560575127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27787772932369203414100169 20840829699276902560575127)
          ·
            refine ⟨31261244548915353840862691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20840829699276902560575127 31261244548915353840862691)
            ·
              refine ⟨46891866823373030761294037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31261244548915353840862691 46891866823373030761294037)
              ·
                refine ⟨1099028128672805408467829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46891866823373030761294037 1099028128672805408467829)
                ·
                  refine ⟨103033887063075507043859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1099028128672805408467829 103033887063075507043859)
                  ·
                    rfl

theorem cell23_1805920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 5].length) (baseStart_1805920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1805920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1805920 prefixEnd_1805920 := by exact prefixLift 1805920
  have htrace : WordTrace (prefixWord ++ tailWord_1805920) baseStart_1805920 baseEnd_1805920 := by
    simpa [prefixWord, tailWord_1805920, baseEnd_1805920] using wordTrace_append hprefix tailTrace_1805920
  have hstable : (prefixWord ++ tailWord_1805920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805920).length < 2 ^ (prefixWord ++ tailWord_1805920).sum := by decide
  have hdescent : baseEnd_1805920 < baseStart_1805920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806077 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_1806077 : Nat := 118140960795 + 1806077 * 2 ^ 59
def prefixEnd_1806077 : Nat := 4983230072969 + 3 ^ 40 * 1806077 * 2
def baseEnd_1806077 : Nat := 927385600030435449131509

theorem tailTrace_1806077 : CollatzResearch.WordTrace tailWord_1806077 prefixEnd_1806077 927385600030435449131509 := by
  unfold tailWord_1806077
  simp only [CollatzResearch.WordTrace]
  refine ⟨65873039877898957239480485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43915359918599304826320323 65873039877898957239480485)
  ·
    refine ⟨12351194977106054482402591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65873039877898957239480485 12351194977106054482402591)
    ·
      refine ⟨18526792465659081723603887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12351194977106054482402591 18526792465659081723603887)
      ·
        refine ⟨27790188698488622585405831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18526792465659081723603887 27790188698488622585405831)
        ·
          refine ⟨41685283047732933878108747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27790188698488622585405831 41685283047732933878108747)
          ·
            refine ⟨62527924571599400817163121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41685283047732933878108747 62527924571599400817163121)
            ·
              refine ⟨46895943428699550612872341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62527924571599400817163121 46895943428699550612872341)
              ·
                refine ⟨2198247348220291434978391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46895943428699550612872341 2198247348220291434978391)
                ·
                  refine ⟨3297371022330437152467587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198247348220291434978391 3297371022330437152467587)
                  ·
                    refine ⟨4946056533495655728701381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3297371022330437152467587 4946056533495655728701381)
                    ·
                      refine ⟨927385600030435449131509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4946056533495655728701381 927385600030435449131509)
                      ·
                        rfl

theorem cell23_1806077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_1806077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806077 prefixEnd_1806077 := by exact prefixLift 1806077
  have htrace : WordTrace (prefixWord ++ tailWord_1806077) baseStart_1806077 baseEnd_1806077 := by
    simpa [prefixWord, tailWord_1806077, baseEnd_1806077] using wordTrace_append hprefix tailTrace_1806077
  have hstable : (prefixWord ++ tailWord_1806077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806077).length < 2 ^ (prefixWord ++ tailWord_1806077).sum := by decide
  have hdescent : baseEnd_1806077 < baseStart_1806077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806080 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 3]
def baseStart_1806080 : Nat := 118140960795 + 1806080 * 2 ^ 59
def prefixEnd_1806080 : Nat := 4983230072969 + 3 ^ 40 * 1806080 * 2
def baseEnd_1806080 : Nat := 927387140472398937393995

theorem tailTrace_1806080 : CollatzResearch.WordTrace tailWord_1806080 prefixEnd_1806080 927387140472398937393995 := by
  unfold tailWord_1806080
  simp only [CollatzResearch.WordTrace]
  refine ⟨32936574648444044375919847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43915432864592059167893129 32936574648444044375919847)
  ·
    refine ⟨49404861972666066563879771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32936574648444044375919847 49404861972666066563879771)
    ·
      refine ⟨74107292958999099845819657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49404861972666066563879771 74107292958999099845819657)
      ·
        refine ⟨55580469719249324884364743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74107292958999099845819657 55580469719249324884364743)
        ·
          refine ⟨83370704578873987326547115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55580469719249324884364743 83370704578873987326547115)
          ·
            refine ⟨125056056868310980989820673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83370704578873987326547115 125056056868310980989820673)
            ·
              refine ⟨93792042651233235742365505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125056056868310980989820673 93792042651233235742365505)
              ·
                refine ⟨70344031988424926806774129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93792042651233235742365505 70344031988424926806774129)
                ·
                  refine ⟨52758023991318695105080597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70344031988424926806774129 52758023991318695105080597)
                  ·
                    refine ⟨2473032374593063833050653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52758023991318695105080597 2473032374593063833050653)
                    ·
                      refine ⟨927387140472398937393995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473032374593063833050653 927387140472398937393995)
                      ·
                        rfl

theorem cell23_1806080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_1806080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806080 prefixEnd_1806080 := by exact prefixLift 1806080
  have htrace : WordTrace (prefixWord ++ tailWord_1806080) baseStart_1806080 baseEnd_1806080 := by
    simpa [prefixWord, tailWord_1806080, baseEnd_1806080] using wordTrace_append hprefix tailTrace_1806080
  have hstable : (prefixWord ++ tailWord_1806080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806080).length < 2 ^ (prefixWord ++ tailWord_1806080).sum := by decide
  have hdescent : baseEnd_1806080 < baseStart_1806080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806117 : List Nat := [1, 3, 1, 2, 3, 4, 1, 8]
def baseStart_1806117 : Nat := 118140960795 + 1806117 * 2 ^ 59
def prefixEnd_1806117 : Nat := 4983230072969 + 3 ^ 40 * 1806117 * 2
def baseEnd_1806117 : Nat := 34348375528022788615975

theorem tailTrace_1806117 : CollatzResearch.WordTrace tailWord_1806117 prefixEnd_1806117 34348375528022788615975 := by
  unfold tailWord_1806117
  simp only [CollatzResearch.WordTrace]
  refine ⟨65874498797754044070936605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43916332531836029380624403 65874498797754044070936605)
  ·
    refine ⟨24702937049157766526601227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65874498797754044070936605 24702937049157766526601227)
    ·
      refine ⟨37054405573736649789901841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24702937049157766526601227 37054405573736649789901841)
      ·
        refine ⟨27790804180302487342426381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37054405573736649789901841 27790804180302487342426381)
        ·
          refine ⟨10421551567613432753409893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27790804180302487342426381 10421551567613432753409893)
          ·
            refine ⟨1954040918927518641264355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10421551567613432753409893 1954040918927518641264355)
            ·
              refine ⟨2931061378391277961896533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954040918927518641264355 2931061378391277961896533)
              ·
                refine ⟨34348375528022788615975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2931061378391277961896533 34348375528022788615975)
                ·
                  rfl

theorem cell23_1806117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 8].length) (baseStart_1806117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806117 prefixEnd_1806117 := by exact prefixLift 1806117
  have htrace : WordTrace (prefixWord ++ tailWord_1806117) baseStart_1806117 baseEnd_1806117 := by
    simpa [prefixWord, tailWord_1806117, baseEnd_1806117] using wordTrace_append hprefix tailTrace_1806117
  have hstable : (prefixWord ++ tailWord_1806117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806117).length < 2 ^ (prefixWord ++ tailWord_1806117).sum := by decide
  have hdescent : baseEnd_1806117 < baseStart_1806117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806161 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 3]
def baseStart_1806161 : Nat := 118140960795 + 1806161 * 2 ^ 59
def prefixEnd_1806161 : Nat := 4983230072969 + 3 ^ 40 * 1806161 * 2
def baseEnd_1806161 : Nat := 927428732405413120481123

theorem tailTrace_1806161 : CollatzResearch.WordTrace tailWord_1806161 prefixEnd_1806161 927428732405413120481123 := by
  unfold tailWord_1806161
  simp only [CollatzResearch.WordTrace]
  refine ⟨65876103609594639585538337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43917402406396426390358891 65876103609594639585538337)
  ·
    refine ⟨49407077707195979689153753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65876103609594639585538337 49407077707195979689153753)
    ·
      refine ⟨37055308280396984766865315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49407077707195979689153753 37055308280396984766865315)
      ·
        refine ⟨55582962420595477150297973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37055308280396984766865315 55582962420595477150297973)
        ·
          refine ⟨5210902726930825982840435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55582962420595477150297973 5210902726930825982840435)
          ·
            refine ⟨7816354090396238974260653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210902726930825982840435 7816354090396238974260653)
            ·
              refine ⟨2931132783898589615347745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7816354090396238974260653 2931132783898589615347745)
              ·
                refine ⟨2198349587923942211510809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2931132783898589615347745 2198349587923942211510809)
                ·
                  refine ⟨1648762190942956658633107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2198349587923942211510809 1648762190942956658633107)
                  ·
                    refine ⟨2473143286414434987949661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1648762190942956658633107 2473143286414434987949661)
                    ·
                      refine ⟨927428732405413120481123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473143286414434987949661 927428732405413120481123)
                      ·
                        rfl

theorem cell23_1806161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_1806161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806161 prefixEnd_1806161 := by exact prefixLift 1806161
  have htrace : WordTrace (prefixWord ++ tailWord_1806161) baseStart_1806161 baseEnd_1806161 := by
    simpa [prefixWord, tailWord_1806161, baseEnd_1806161] using wordTrace_append hprefix tailTrace_1806161
  have hstable : (prefixWord ++ tailWord_1806161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806161).length < 2 ^ (prefixWord ++ tailWord_1806161).sum := by decide
  have hdescent : baseEnd_1806161 < baseStart_1806161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806311 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1806311 : Nat := 118140960795 + 1806311 * 2 ^ 59
def prefixEnd_1806311 : Nat := 4983230072969 + 3 ^ 40 * 1806311 * 2
def baseEnd_1806311 : Nat := 927505754503587533605433

theorem tailTrace_1806311 : CollatzResearch.WordTrace tailWord_1806311 prefixEnd_1806311 927505754503587533605433 := by
  unfold tailWord_1806311
  simp only [CollatzResearch.WordTrace]
  refine ⟨65881574559051215203498787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43921049706034143468999191 65881574559051215203498787)
  ·
    refine ⟨98822361838576822805248181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65881574559051215203498787 98822361838576822805248181)
    ·
      refine ⟨9264596422366577137992017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98822361838576822805248181 9264596422366577137992017)
      ·
        refine ⟨6948447316774932853494013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9264596422366577137992017 6948447316774932853494013)
        ·
          refine ⟨2605667743790599820060255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6948447316774932853494013 2605667743790599820060255)
          ·
            refine ⟨3908501615685899730090383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605667743790599820060255 3908501615685899730090383)
            ·
              refine ⟨5862752423528849595135575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908501615685899730090383 5862752423528849595135575)
              ·
                refine ⟨8794128635293274392703363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862752423528849595135575 8794128635293274392703363)
                ·
                  refine ⟨13191192952939911589055045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8794128635293274392703363 13191192952939911589055045)
                  ·
                    refine ⟨2473348678676233422947821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13191192952939911589055045 2473348678676233422947821)
                    ·
                      refine ⟨927505754503587533605433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473348678676233422947821 927505754503587533605433)
                      ·
                        rfl

theorem cell23_1806311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1806311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806311 prefixEnd_1806311 := by exact prefixLift 1806311
  have htrace : WordTrace (prefixWord ++ tailWord_1806311) baseStart_1806311 baseEnd_1806311 := by
    simpa [prefixWord, tailWord_1806311, baseEnd_1806311] using wordTrace_append hprefix tailTrace_1806311
  have hstable : (prefixWord ++ tailWord_1806311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806311).length < 2 ^ (prefixWord ++ tailWord_1806311).sum := by decide
  have hdescent : baseEnd_1806311 < baseStart_1806311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806318 : List Nat := [4, 1, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_1806318 : Nat := 118140960795 + 1806318 * 2 ^ 59
def prefixEnd_1806318 : Nat := 4983230072969 + 3 ^ 40 * 1806318 * 2
def baseEnd_1806318 : Nat := 309169782956056335405967

theorem tailTrace_1806318 : CollatzResearch.WordTrace tailWord_1806318 prefixEnd_1806318 309169782956056335405967 := by
  unfold tailWord_1806318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235228733753231924875451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43921219913350570266002405 8235228733753231924875451)
  ·
    refine ⟨12352843100629847887313177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8235228733753231924875451 12352843100629847887313177)
    ·
      refine ⟨9264632325472385915484883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12352843100629847887313177 9264632325472385915484883)
      ·
        refine ⟨13896948488208578873227325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9264632325472385915484883 13896948488208578873227325)
        ·
          refine ⟨5211355683078217077460247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13896948488208578873227325 5211355683078217077460247)
          ·
            refine ⟨7817033524617325616190371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5211355683078217077460247 7817033524617325616190371)
            ·
              refine ⟨11725550286925988424285557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817033524617325616190371 11725550286925988424285557)
              ·
                refine ⟨1099270339399311414776771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11725550286925988424285557 1099270339399311414776771)
                ·
                  refine ⟨1648905509098967122165157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099270339399311414776771 1648905509098967122165157)
                  ·
                    refine ⟨309169782956056335405967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1648905509098967122165157 309169782956056335405967)
                    ·
                      rfl

theorem cell23_1806318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_1806318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806318 prefixEnd_1806318 := by exact prefixLift 1806318
  have htrace : WordTrace (prefixWord ++ tailWord_1806318) baseStart_1806318 baseEnd_1806318 := by
    simpa [prefixWord, tailWord_1806318, baseEnd_1806318] using wordTrace_append hprefix tailTrace_1806318
  have hstable : (prefixWord ++ tailWord_1806318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806318).length < 2 ^ (prefixWord ++ tailWord_1806318).sum := by decide
  have hdescent : baseEnd_1806318 < baseStart_1806318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806341 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 3]
def baseStart_1806341 : Nat := 118140960795 + 1806341 * 2 ^ 59
def prefixEnd_1806341 : Nat := 4983230072969 + 3 ^ 40 * 1806341 * 2
def baseEnd_1806341 : Nat := 927521158923222416230295

theorem tailTrace_1806341 : CollatzResearch.WordTrace tailWord_1806341 prefixEnd_1806341 927521158923222416230295 := by
  unfold tailWord_1806341
  simp only [CollatzResearch.WordTrace]
  refine ⟨65882668748942530327090877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43921779165961686884727251 65882668748942530327090877)
  ·
    refine ⟨24706000780853448872659079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65882668748942530327090877 24706000780853448872659079)
    ·
      refine ⟨37059001171280173308988619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24706000780853448872659079 37059001171280173308988619)
      ·
        refine ⟨55588501756920259963482929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37059001171280173308988619 55588501756920259963482929)
        ·
          refine ⟨41691376317690194972612197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55588501756920259963482929 41691376317690194972612197)
          ·
            refine ⟨7817133059566911557364787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41691376317690194972612197 7817133059566911557364787)
            ·
              refine ⟨11725699589350367336047181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817133059566911557364787 11725699589350367336047181)
              ·
                refine ⟨4397137346006387751017693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11725699589350367336047181 4397137346006387751017693)
                ·
                  refine ⟨1648926504752395406631635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4397137346006387751017693 1648926504752395406631635)
                  ·
                    refine ⟨2473389757128593109947453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1648926504752395406631635 2473389757128593109947453)
                    ·
                      refine ⟨927521158923222416230295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473389757128593109947453 927521158923222416230295)
                      ·
                        rfl

theorem cell23_1806341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_1806341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806341 prefixEnd_1806341 := by exact prefixLift 1806341
  have htrace : WordTrace (prefixWord ++ tailWord_1806341) baseStart_1806341 baseEnd_1806341 := by
    simpa [prefixWord, tailWord_1806341, baseEnd_1806341] using wordTrace_append hprefix tailTrace_1806341
  have hstable : (prefixWord ++ tailWord_1806341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806341).length < 2 ^ (prefixWord ++ tailWord_1806341).sum := by decide
  have hdescent : baseEnd_1806341 < baseStart_1806341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806384 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_1806384 : Nat := 118140960795 + 1806384 * 2 ^ 59
def prefixEnd_1806384 : Nat := 4983230072969 + 3 ^ 40 * 1806384 * 2
def baseEnd_1806384 : Nat := 927543238591365747992597

theorem tailTrace_1806384 : CollatzResearch.WordTrace tailWord_1806384 prefixEnd_1806384 927543238591365747992597 := by
  unfold tailWord_1806384
  simp only [CollatzResearch.WordTrace]
  refine ⟨32942118543893374335453103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43922824725191165780604137 32942118543893374335453103)
  ·
    refine ⟨49413177815840061503179655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32942118543893374335453103 49413177815840061503179655)
    ·
      refine ⟨74119766723760092254769483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49413177815840061503179655 74119766723760092254769483)
      ·
        refine ⟨111179650085640138382154225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74119766723760092254769483 111179650085640138382154225)
        ·
          refine ⟨83384737564230103786615669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111179650085640138382154225 83384737564230103786615669)
          ·
            refine ⟨7817319146646572229995219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83384737564230103786615669 7817319146646572229995219)
            ·
              refine ⟨11725978719969858344992829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817319146646572229995219 11725978719969858344992829)
              ·
                refine ⟨4397242019988696879372311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11725978719969858344992829 4397242019988696879372311)
                ·
                  refine ⟨6595863029983045319058467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397242019988696879372311 6595863029983045319058467)
                  ·
                    refine ⟨9893794544974567978587701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595863029983045319058467 9893794544974567978587701)
                    ·
                      refine ⟨927543238591365747992597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9893794544974567978587701 927543238591365747992597)
                      ·
                        rfl

theorem cell23_1806384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_1806384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806384 prefixEnd_1806384 := by exact prefixLift 1806384
  have htrace : WordTrace (prefixWord ++ tailWord_1806384) baseStart_1806384 baseEnd_1806384 := by
    simpa [prefixWord, tailWord_1806384, baseEnd_1806384] using wordTrace_append hprefix tailTrace_1806384
  have hstable : (prefixWord ++ tailWord_1806384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806384).length < 2 ^ (prefixWord ++ tailWord_1806384).sum := by decide
  have hdescent : baseEnd_1806384 < baseStart_1806384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806387 : List Nat := [1, 1, 1, 2, 4, 1, 13]
def baseStart_1806387 : Nat := 118140960795 + 1806387 * 2 ^ 59
def prefixEnd_1806387 : Nat := 4983230072969 + 3 ^ 40 * 1806387 * 2
def baseEnd_1806387 : Nat := 11451170111522583163643

theorem tailTrace_1806387 : CollatzResearch.WordTrace tailWord_1806387 prefixEnd_1806387 11451170111522583163643 := by
  unfold tailWord_1806387
  simp only [CollatzResearch.WordTrace]
  refine ⟨65884346506775880183265415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43922897671183920122176943 65884346506775880183265415)
  ·
    refine ⟨98826519760163820274898123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65884346506775880183265415 98826519760163820274898123)
    ·
      refine ⟨148239779640245730412347185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98826519760163820274898123 148239779640245730412347185)
      ·
        refine ⟨111179834730184297809260389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148239779640245730412347185 111179834730184297809260389)
        ·
          refine ⟨20846219011909555839236323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111179834730184297809260389 20846219011909555839236323)
          ·
            refine ⟨31269328517864333758854485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20846219011909555839236323 31269328517864333758854485)
            ·
              refine ⟨11451170111522583163643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 31269328517864333758854485 11451170111522583163643)
              ·
                rfl

theorem cell23_1806387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 13].length) (baseStart_1806387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806387 prefixEnd_1806387 := by exact prefixLift 1806387
  have htrace : WordTrace (prefixWord ++ tailWord_1806387) baseStart_1806387 baseEnd_1806387 := by
    simpa [prefixWord, tailWord_1806387, baseEnd_1806387] using wordTrace_append hprefix tailTrace_1806387
  have hstable : (prefixWord ++ tailWord_1806387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806387).length < 2 ^ (prefixWord ++ tailWord_1806387).sum := by decide
  have hdescent : baseEnd_1806387 < baseStart_1806387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806392 : List Nat := [2, 1, 2, 1, 6, 1, 3, 2, 1, 1, 3]
def baseStart_1806392 : Nat := 118140960795 + 1806392 * 2 ^ 59
def prefixEnd_1806392 : Nat := 4983230072969 + 3 ^ 40 * 1806392 * 2
def baseEnd_1806392 : Nat := 927547346436601716692561

theorem tailTrace_1806392 : CollatzResearch.WordTrace tailWord_1806392 prefixEnd_1806392 927547346436601716692561 := by
  unfold tailWord_1806392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32942264435878883018598715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43923019247838510691464953 32942264435878883018598715)
  ·
    refine ⟨49413396653818324527898073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32942264435878883018598715 49413396653818324527898073)
    ·
      refine ⟨37060047490363743395923555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49413396653818324527898073 37060047490363743395923555)
      ·
        refine ⟨55590071235545615093885333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37060047490363743395923555 55590071235545615093885333)
        ·
          refine ⟨2605784589166200707525875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55590071235545615093885333 2605784589166200707525875)
          ·
            refine ⟨3908676883749301061288813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605784589166200707525875 3908676883749301061288813)
            ·
              refine ⟨1465753831405987897983305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3908676883749301061288813 1465753831405987897983305)
              ·
                refine ⟨1099315373554490923487479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465753831405987897983305 1099315373554490923487479)
                ·
                  refine ⟨1648973060331736385231219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099315373554490923487479 1648973060331736385231219)
                  ·
                    refine ⟨2473459590497604577846829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1648973060331736385231219 2473459590497604577846829)
                    ·
                      refine ⟨927547346436601716692561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473459590497604577846829 927547346436601716692561)
                      ·
                        rfl

theorem cell23_1806392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 1, 3].length) (baseStart_1806392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806392 prefixEnd_1806392 := by exact prefixLift 1806392
  have htrace : WordTrace (prefixWord ++ tailWord_1806392) baseStart_1806392 baseEnd_1806392 := by
    simpa [prefixWord, tailWord_1806392, baseEnd_1806392] using wordTrace_append hprefix tailTrace_1806392
  have hstable : (prefixWord ++ tailWord_1806392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806392).length < 2 ^ (prefixWord ++ tailWord_1806392).sum := by decide
  have hdescent : baseEnd_1806392 < baseStart_1806392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806401 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1806401 : Nat := 118140960795 + 1806401 * 2 ^ 59
def prefixEnd_1806401 : Nat := 4983230072969 + 3 ^ 40 * 1806401 * 2
def baseEnd_1806401 : Nat := 927551967762492181480019

theorem tailTrace_1806401 : CollatzResearch.WordTrace tailWord_1806401 prefixEnd_1806401 927551967762492181480019 := by
  unfold tailWord_1806401
  simp only [CollatzResearch.WordTrace]
  refine ⟨65884857128725160574275057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43923238085816773716183371 65884857128725160574275057)
  ·
    refine ⟨49413642846543870430706293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65884857128725160574275057 49413642846543870430706293)
    ·
      refine ⟨4632529016863487852878715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49413642846543870430706293 4632529016863487852878715)
      ·
        refine ⟨6948793525295231779318073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4632529016863487852878715 6948793525295231779318073)
        ·
          refine ⟨5211595143971423834488555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6948793525295231779318073 5211595143971423834488555)
          ·
            refine ⟨7817392715957135751732833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5211595143971423834488555 7817392715957135751732833)
            ·
              refine ⟨5863044536967851813799625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7817392715957135751732833 5863044536967851813799625)
              ·
                refine ⟨4397283402725888860349719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5863044536967851813799625 4397283402725888860349719)
                ·
                  refine ⟨6595925104088833290524579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397283402725888860349719 6595925104088833290524579)
                  ·
                    refine ⟨9893887656133249935786869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595925104088833290524579 9893887656133249935786869)
                    ·
                      refine ⟨927551967762492181480019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9893887656133249935786869 927551967762492181480019)
                      ·
                        rfl

theorem cell23_1806401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1806401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806401 prefixEnd_1806401 := by exact prefixLift 1806401
  have htrace : WordTrace (prefixWord ++ tailWord_1806401) baseStart_1806401 baseEnd_1806401 := by
    simpa [prefixWord, tailWord_1806401, baseEnd_1806401] using wordTrace_append hprefix tailTrace_1806401
  have hstable : (prefixWord ++ tailWord_1806401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806401).length < 2 ^ (prefixWord ++ tailWord_1806401).sum := by decide
  have hdescent : baseEnd_1806401 < baseStart_1806401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806418 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_1806418 : Nat := 118140960795 + 1806418 * 2 ^ 59
def prefixEnd_1806418 : Nat := 4983230072969 + 3 ^ 40 * 1806418 * 2
def baseEnd_1806418 : Nat := 927560696933618614967441

theorem tailTrace_1806418 : CollatzResearch.WordTrace tailWord_1806418 prefixEnd_1806418 927560696933618614967441 := by
  unfold tailWord_1806418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16471369292415893119410977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43923651446442381651762605 16471369292415893119410977)
  ·
    refine ⟨12353526969311919839558233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16471369292415893119410977 12353526969311919839558233)
    ·
      refine ⟨9265145226983939879668675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12353526969311919839558233 9265145226983939879668675)
      ·
        refine ⟨13897717840475909819503013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9265145226983939879668675 13897717840475909819503013)
        ·
          refine ⟨2605822095089233091156815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13897717840475909819503013 2605822095089233091156815)
          ·
            refine ⟨3908733142633849636735223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605822095089233091156815 3908733142633849636735223)
            ·
              refine ⟨5863099713950774455102835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908733142633849636735223 5863099713950774455102835)
              ·
                refine ⟨8794649570926161682654253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5863099713950774455102835 8794649570926161682654253)
                ·
                  refine ⟨3297993589097310630995345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8794649570926161682654253 3297993589097310630995345)
                  ·
                    refine ⟨2473495191822982973246509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3297993589097310630995345 2473495191822982973246509)
                    ·
                      refine ⟨927560696933618614967441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473495191822982973246509 927560696933618614967441)
                      ·
                        rfl

theorem cell23_1806418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_1806418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806418 prefixEnd_1806418 := by exact prefixLift 1806418
  have htrace : WordTrace (prefixWord ++ tailWord_1806418) baseStart_1806418 baseEnd_1806418 := by
    simpa [prefixWord, tailWord_1806418, baseEnd_1806418] using wordTrace_append hprefix tailTrace_1806418
  have hstable : (prefixWord ++ tailWord_1806418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806418).length < 2 ^ (prefixWord ++ tailWord_1806418).sum := by decide
  have hdescent : baseEnd_1806418 < baseStart_1806418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806431 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 3]
def baseStart_1806431 : Nat := 118140960795 + 1806431 * 2 ^ 59
def prefixEnd_1806431 : Nat := 4983230072969 + 3 ^ 40 * 1806431 * 2
def baseEnd_1806431 : Nat := 927567372182127064104881

theorem tailTrace_1806431 : CollatzResearch.WordTrace tailWord_1806431 prefixEnd_1806431 927567372182127064104881 := by
  unfold tailWord_1806431
  simp only [CollatzResearch.WordTrace]
  refine ⟨65885951318616475697867147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43923967545744317131911431 65885951318616475697867147)
  ·
    refine ⟨98828926977924713546800721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65885951318616475697867147 98828926977924713546800721)
    ·
      refine ⟨74121695233443535160100541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98828926977924713546800721 74121695233443535160100541)
      ·
        refine ⟨27795635712541325685037703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74121695233443535160100541 27795635712541325685037703)
        ·
          refine ⟨41693453568811988527556555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27795635712541325685037703 41693453568811988527556555)
          ·
            refine ⟨62540180353217982791334833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41693453568811988527556555 62540180353217982791334833)
            ·
              refine ⟨46905135264913487093501125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62540180353217982791334833 46905135264913487093501125)
              ·
                refine ⟨8794712862171278830031461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46905135264913487093501125 8794712862171278830031461)
                ·
                  refine ⟨1649008661657114780630899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8794712862171278830031461 1649008661657114780630899)
                  ·
                    refine ⟨2473512992485672170946349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1649008661657114780630899 2473512992485672170946349)
                    ·
                      refine ⟨927567372182127064104881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473512992485672170946349 927567372182127064104881)
                      ·
                        rfl

theorem cell23_1806431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_1806431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806431 prefixEnd_1806431 := by exact prefixLift 1806431
  have htrace : WordTrace (prefixWord ++ tailWord_1806431) baseStart_1806431 baseEnd_1806431 := by
    simpa [prefixWord, tailWord_1806431, baseEnd_1806431] using wordTrace_append hprefix tailTrace_1806431
  have hstable : (prefixWord ++ tailWord_1806431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806431).length < 2 ^ (prefixWord ++ tailWord_1806431).sum := by decide
  have hdescent : baseEnd_1806431 < baseStart_1806431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806448 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 2, 1, 3]
def baseStart_1806448 : Nat := 118140960795 + 1806448 * 2 ^ 59
def prefixEnd_1806448 : Nat := 4983230072969 + 3 ^ 40 * 1806448 * 2
def baseEnd_1806448 : Nat := 927576101353253497592303

theorem tailTrace_1806448 : CollatzResearch.WordTrace tailWord_1806448 prefixEnd_1806448 927576101353253497592303 := by
  unfold tailWord_1806448
  simp only [CollatzResearch.WordTrace]
  refine ⟨32943285679777443800617999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43924380906369925067490665 32943285679777443800617999)
  ·
    refine ⟨49414928519666165700926999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32943285679777443800617999 49414928519666165700926999)
    ·
      refine ⟨74122392779499248551390499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49414928519666165700926999 74122392779499248551390499)
      ·
        refine ⟨111183589169248872827085749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74122392779499248551390499 111183589169248872827085749)
        ·
          refine ⟨10423461484617081827539289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111183589169248872827085749 10423461484617081827539289)
          ·
            refine ⟨7817596113462811370654467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10423461484617081827539289 7817596113462811370654467)
            ·
              refine ⟨11726394170194217055981701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817596113462811370654467 11726394170194217055981701)
              ·
                refine ⟨2198698906911415697996569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11726394170194217055981701 2198698906911415697996569)
                ·
                  refine ⟨1649024180183561773497427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2198698906911415697996569 1649024180183561773497427)
                  ·
                    refine ⟨2473536270275342660246141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1649024180183561773497427 2473536270275342660246141)
                    ·
                      refine ⟨927576101353253497592303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473536270275342660246141 927576101353253497592303)
                      ·
                        rfl

theorem cell23_1806448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 1, 3].length) (baseStart_1806448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806448 prefixEnd_1806448 := by exact prefixLift 1806448
  have htrace : WordTrace (prefixWord ++ tailWord_1806448) baseStart_1806448 baseEnd_1806448 := by
    simpa [prefixWord, tailWord_1806448, baseEnd_1806448] using wordTrace_append hprefix tailTrace_1806448
  have hstable : (prefixWord ++ tailWord_1806448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806448).length < 2 ^ (prefixWord ++ tailWord_1806448).sum := by decide
  have hdescent : baseEnd_1806448 < baseStart_1806448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806486 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1806486 : Nat := 118140960795 + 1806486 * 2 ^ 59
def prefixEnd_1806486 : Nat := 4983230072969 + 3 ^ 40 * 1806486 * 2
def baseEnd_1806486 : Nat := 927595613618124348917129

theorem tailTrace_1806486 : CollatzResearch.WordTrace tailWord_1806486 prefixEnd_1806486 927595613618124348917129 := by
  unfold tailWord_1806486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117997333338576255694957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43925304888944813394079541 4117997333338576255694957)
  ·
    refine ⟨1544249000001966095885609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4117997333338576255694957 1544249000001966095885609)
    ·
      refine ⟨1158186750001474571914207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1544249000001966095885609 1158186750001474571914207)
      ·
        refine ⟨1737280125002211857871311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158186750001474571914207 1737280125002211857871311)
        ·
          refine ⟨2605920187503317786806967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737280125002211857871311 2605920187503317786806967)
          ·
            refine ⟨3908880281254976680210451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605920187503317786806967 3908880281254976680210451)
            ·
              refine ⟨5863320421882465020315677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908880281254976680210451 5863320421882465020315677)
              ·
                refine ⟨2198745158205924382618379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5863320421882465020315677 2198745158205924382618379)
                ·
                  refine ⟨3298117737308886573927569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198745158205924382618379 3298117737308886573927569)
                  ·
                    refine ⟨2473588302981664930445677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3298117737308886573927569 2473588302981664930445677)
                    ·
                      refine ⟨927595613618124348917129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473588302981664930445677 927595613618124348917129)
                      ·
                        rfl

theorem cell23_1806486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1806486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806486 prefixEnd_1806486 := by exact prefixLift 1806486
  have htrace : WordTrace (prefixWord ++ tailWord_1806486) baseStart_1806486 baseEnd_1806486 := by
    simpa [prefixWord, tailWord_1806486, baseEnd_1806486] using wordTrace_append hprefix tailTrace_1806486
  have hstable : (prefixWord ++ tailWord_1806486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806486).length < 2 ^ (prefixWord ++ tailWord_1806486).sum := by decide
  have hdescent : baseEnd_1806486 < baseStart_1806486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806516 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1806516 : Nat := 118140960795 + 1806516 * 2 ^ 59
def prefixEnd_1806516 : Nat := 4983230072969 + 3 ^ 40 * 1806516 * 2
def baseEnd_1806516 : Nat := 927611018037759231541991

theorem tailTrace_1806516 : CollatzResearch.WordTrace tailWord_1806516 prefixEnd_1806516 927611018037759231541991 := by
  unfold tailWord_1806516
  simp only [CollatzResearch.WordTrace]
  refine ⟨32944525761654267607355701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43926034348872356809807601 32944525761654267607355701)
  ·
    refine ⟨3088549290155087588189597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32944525761654267607355701 3088549290155087588189597)
    ·
      refine ⟨1158205983808157845571099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3088549290155087588189597 1158205983808157845571099)
      ·
        refine ⟨1737308975712236768356649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158205983808157845571099 1737308975712236768356649)
        ·
          refine ⟨1302981731784177576267487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1737308975712236768356649 1302981731784177576267487)
          ·
            refine ⟨1954472597676266364401231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302981731784177576267487 1954472597676266364401231)
            ·
              refine ⟨2931708896514399546601847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954472597676266364401231 2931708896514399546601847)
              ·
                refine ⟨4397563344771599319902771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931708896514399546601847 4397563344771599319902771)
                ·
                  refine ⟨6596345017157398979854157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397563344771599319902771 6596345017157398979854157)
                  ·
                    refine ⟨2473629381434024617445309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6596345017157398979854157 2473629381434024617445309)
                    ·
                      refine ⟨927611018037759231541991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473629381434024617445309 927611018037759231541991)
                      ·
                        rfl

theorem cell23_1806516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1806516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806516 prefixEnd_1806516 := by exact prefixLift 1806516
  have htrace : WordTrace (prefixWord ++ tailWord_1806516) baseStart_1806516 baseEnd_1806516 := by
    simpa [prefixWord, tailWord_1806516, baseEnd_1806516] using wordTrace_append hprefix tailTrace_1806516
  have hstable : (prefixWord ++ tailWord_1806516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806516).length < 2 ^ (prefixWord ++ tailWord_1806516).sum := by decide
  have hdescent : baseEnd_1806516 < baseStart_1806516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806521 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1806521 : Nat := 118140960795 + 1806521 * 2 ^ 59
def prefixEnd_1806521 : Nat := 4983230072969 + 3 ^ 40 * 1806521 * 2
def baseEnd_1806521 : Nat := 927613585441031711979467

theorem tailTrace_1806521 : CollatzResearch.WordTrace tailWord_1806521 prefixEnd_1806521 927613585441031711979467 := by
  unfold tailWord_1806521
  simp only [CollatzResearch.WordTrace]
  refine ⟨65889233888290421068643417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43926155925526947379095611 65889233888290421068643417)
  ·
    refine ⟨49416925416217815801482563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65889233888290421068643417 49416925416217815801482563)
    ·
      refine ⟨74125388124326723702223845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49416925416217815801482563 74125388124326723702223845)
      ·
        refine ⟨13898510273311260694166971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74125388124326723702223845 13898510273311260694166971)
        ·
          refine ⟨20847765409966891041250457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13898510273311260694166971 20847765409966891041250457)
          ·
            refine ⟨15635824057475168280937843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20847765409966891041250457 15635824057475168280937843)
            ·
              refine ⟨23453736086212752421406765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15635824057475168280937843 23453736086212752421406765)
              ·
                refine ⟨8795151032329782158027537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23453736086212752421406765 8795151032329782158027537)
                ·
                  refine ⟨6596363274247336618520653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8795151032329782158027537 6596363274247336618520653)
                  ·
                    refine ⟨2473636227842751231945245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6596363274247336618520653 2473636227842751231945245)
                    ·
                      refine ⟨927613585441031711979467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473636227842751231945245 927613585441031711979467)
                      ·
                        rfl

theorem cell23_1806521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1806521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806521 prefixEnd_1806521 := by exact prefixLift 1806521
  have htrace : WordTrace (prefixWord ++ tailWord_1806521) baseStart_1806521 baseEnd_1806521 := by
    simpa [prefixWord, tailWord_1806521, baseEnd_1806521] using wordTrace_append hprefix tailTrace_1806521
  have hstable : (prefixWord ++ tailWord_1806521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806521).length < 2 ^ (prefixWord ++ tailWord_1806521).sum := by decide
  have hdescent : baseEnd_1806521 < baseStart_1806521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806531 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 3, 7, 2]
def baseStart_1806531 : Nat := 118140960795 + 1806531 * 2 ^ 59
def prefixEnd_1806531 : Nat := 4983230072969 + 3 ^ 40 * 1806531 * 2
def baseEnd_1806531 : Nat := 927618720247576672854421

theorem tailTrace_1806531 : CollatzResearch.WordTrace tailWord_1806531 prefixEnd_1806531 927618720247576672854421 := by
  unfold tailWord_1806531
  simp only [CollatzResearch.WordTrace]
  refine ⟨65889598618254192776507447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43926399078836128517671631 65889598618254192776507447)
  ·
    refine ⟨98834397927381289164761171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65889598618254192776507447 98834397927381289164761171)
    ·
      refine ⟨148251596891071933747141757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98834397927381289164761171 148251596891071933747141757)
      ·
        refine ⟨55594348834151975155178159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148251596891071933747141757 55594348834151975155178159)
        ·
          refine ⟨83391523251227962732767239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55594348834151975155178159 83391523251227962732767239)
          ·
            refine ⟨125087284876841944099150859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83391523251227962732767239 125087284876841944099150859)
            ·
              refine ⟨187630927315262916148726289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125087284876841944099150859 187630927315262916148726289)
              ·
                refine ⟨140723195486447187111544717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187630927315262916148726289 140723195486447187111544717)
                ·
                  refine ⟨52771198307417695166829269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140723195486447187111544717 52771198307417695166829269)
                  ·
                    refine ⟨1236824960330102230472561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52771198307417695166829269 1236824960330102230472561)
                    ·
                      refine ⟨927618720247576672854421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1236824960330102230472561 927618720247576672854421)
                      ·
                        rfl

theorem cell23_1806531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_1806531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806531 prefixEnd_1806531 := by exact prefixLift 1806531
  have htrace : WordTrace (prefixWord ++ tailWord_1806531) baseStart_1806531 baseEnd_1806531 := by
    simpa [prefixWord, tailWord_1806531, baseEnd_1806531] using wordTrace_append hprefix tailTrace_1806531
  have hstable : (prefixWord ++ tailWord_1806531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806531).length < 2 ^ (prefixWord ++ tailWord_1806531).sum := by decide
  have hdescent : baseEnd_1806531 < baseStart_1806531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806645 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_1806645 : Nat := 118140960795 + 1806645 * 2 ^ 59
def prefixEnd_1806645 : Nat := 4983230072969 + 3 ^ 40 * 1806645 * 2
def baseEnd_1806645 : Nat := 927677257042189226828897

theorem tailTrace_1806645 : CollatzResearch.WordTrace tailWord_1806645 prefixEnd_1806645 927677257042189226828897 := by
  unfold tailWord_1806645
  simp only [CollatzResearch.WordTrace]
  refine ⟨65893756539841190246157389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43929171026560793497438259 65893756539841190246157389)
  ·
    refine ⟨24710158702440446342309021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65893756539841190246157389 24710158702440446342309021)
    ·
      refine ⟨9266309513415167378365883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24710158702440446342309021 9266309513415167378365883)
      ·
        refine ⟨13899464270122751067548825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9266309513415167378365883 13899464270122751067548825)
        ·
          refine ⟨10424598202592063300661619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13899464270122751067548825 10424598202592063300661619)
          ·
            refine ⟨15636897303888094950992429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10424598202592063300661619 15636897303888094950992429)
            ·
              refine ⟨5863836488958035606622161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15636897303888094950992429 5863836488958035606622161)
              ·
                refine ⟨4397877366718526704966621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5863836488958035606622161 4397877366718526704966621)
                ·
                  refine ⟨1649204012519447514362483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4397877366718526704966621 1649204012519447514362483)
                  ·
                    refine ⟨2473806018779171271543725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1649204012519447514362483 2473806018779171271543725)
                    ·
                      refine ⟨927677257042189226828897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473806018779171271543725 927677257042189226828897)
                      ·
                        rfl

theorem cell23_1806645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_1806645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806645 prefixEnd_1806645 := by exact prefixLift 1806645
  have htrace : WordTrace (prefixWord ++ tailWord_1806645) baseStart_1806645 baseEnd_1806645 := by
    simpa [prefixWord, tailWord_1806645, baseEnd_1806645] using wordTrace_append hprefix tailTrace_1806645
  have hstable : (prefixWord ++ tailWord_1806645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806645).length < 2 ^ (prefixWord ++ tailWord_1806645).sum := by decide
  have hdescent : baseEnd_1806645 < baseStart_1806645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806681 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_1806681 : Nat := 118140960795 + 1806681 * 2 ^ 59
def prefixEnd_1806681 : Nat := 4983230072969 + 3 ^ 40 * 1806681 * 2
def baseEnd_1806681 : Nat := 927695742345751085978731

theorem tailTrace_1806681 : CollatzResearch.WordTrace tailWord_1806681 prefixEnd_1806681 927695742345751085978731 := by
  unfold tailWord_1806681
  simp only [CollatzResearch.WordTrace]
  refine ⟨65895069567710768394467897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43930046378473845596311931 65895069567710768394467897)
  ·
    refine ⟨49421302175783076295850923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65895069567710768394467897 49421302175783076295850923)
    ·
      refine ⟨74131953263674614443776385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49421302175783076295850923 74131953263674614443776385)
      ·
        refine ⟨55598964947755960832832289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74131953263674614443776385 55598964947755960832832289)
        ·
          refine ⟨41699223710816970624624217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55598964947755960832832289 41699223710816970624624217)
          ·
            refine ⟨31274417783112727968468163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41699223710816970624624217 31274417783112727968468163)
            ·
              refine ⟨46911626674669091952702245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31274417783112727968468163 46911626674669091952702245)
              ·
                refine ⟨8795930001500454741131671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46911626674669091952702245 8795930001500454741131671)
                ·
                  refine ⟨13193895002250682111697507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8795930001500454741131671 13193895002250682111697507)
                  ·
                    refine ⟨19790842503376023167546261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13193895002250682111697507 19790842503376023167546261)
                    ·
                      refine ⟨927695742345751085978731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19790842503376023167546261 927695742345751085978731)
                      ·
                        rfl

theorem cell23_1806681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_1806681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806681 prefixEnd_1806681 := by exact prefixLift 1806681
  have htrace : WordTrace (prefixWord ++ tailWord_1806681) baseStart_1806681 baseEnd_1806681 := by
    simpa [prefixWord, tailWord_1806681, baseEnd_1806681] using wordTrace_append hprefix tailTrace_1806681
  have hstable : (prefixWord ++ tailWord_1806681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806681).length < 2 ^ (prefixWord ++ tailWord_1806681).sum := by decide
  have hdescent : baseEnd_1806681 < baseStart_1806681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806691 : List Nat := [1, 1, 1, 5, 2, 1, 2, 10]
def baseStart_1806691 : Nat := 118140960795 + 1806691 * 2 ^ 59
def prefixEnd_1806691 : Nat := 4983230072969 + 3 ^ 40 * 1806691 * 2
def baseEnd_1806691 : Nat := 34359291746381335068655

theorem tailTrace_1806691 : CollatzResearch.WordTrace tailWord_1806691 prefixEnd_1806691 34359291746381335068655 := by
  unfold tailWord_1806691
  simp only [CollatzResearch.WordTrace]
  refine ⟨65895434297674540102331927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43930289531783026734887951 65895434297674540102331927)
  ·
    refine ⟨98843151446511810153497891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65895434297674540102331927 98843151446511810153497891)
    ·
      refine ⟨148264727169767715230246837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98843151446511810153497891 148264727169767715230246837)
      ·
        refine ⟨13899818172165723302835641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148264727169767715230246837 13899818172165723302835641)
        ·
          refine ⟨10424863629124292477126731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13899818172165723302835641 10424863629124292477126731)
          ·
            refine ⟨15637295443686438715690097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10424863629124292477126731 15637295443686438715690097)
            ·
              refine ⟨11727971582764829036767573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15637295443686438715690097 11727971582764829036767573)
              ·
                refine ⟨34359291746381335068655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11727971582764829036767573 34359291746381335068655)
                ·
                  rfl

theorem cell23_1806691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 10].length) (baseStart_1806691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806691 prefixEnd_1806691 := by exact prefixLift 1806691
  have htrace : WordTrace (prefixWord ++ tailWord_1806691) baseStart_1806691 baseEnd_1806691 := by
    simpa [prefixWord, tailWord_1806691, baseEnd_1806691] using wordTrace_append hprefix tailTrace_1806691
  have hstable : (prefixWord ++ tailWord_1806691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806691).length < 2 ^ (prefixWord ++ tailWord_1806691).sum := by decide
  have hdescent : baseEnd_1806691 < baseStart_1806691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806695 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 1, 6]
def baseStart_1806695 : Nat := 118140960795 + 1806695 * 2 ^ 59
def prefixEnd_1806695 : Nat := 4983230072969 + 3 ^ 40 * 1806695 * 2
def baseEnd_1806695 : Nat := 309234310358304677067889

theorem tailTrace_1806695 : CollatzResearch.WordTrace tailWord_1806695 prefixEnd_1806695 309234310358304677067889 := by
  unfold tailWord_1806695
  simp only [CollatzResearch.WordTrace]
  refine ⟨65895580189660048785477539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43930386793106699190318359 65895580189660048785477539)
  ·
    refine ⟨98843370284490073178216309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65895580189660048785477539 98843370284490073178216309)
    ·
      refine ⟨9266565964170944360457779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98843370284490073178216309 9266565964170944360457779)
      ·
        refine ⟨13899848946256416540686669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9266565964170944360457779 13899848946256416540686669)
        ·
          refine ⟨5212443354846156202757501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13899848946256416540686669 5212443354846156202757501)
          ·
            refine ⟨1954666258067308576034063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5212443354846156202757501 1954666258067308576034063)
            ·
              refine ⟨2931999387100962864051095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954666258067308576034063 2931999387100962864051095)
              ·
                refine ⟨4397999080651444296076643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931999387100962864051095 4397999080651444296076643)
                ·
                  refine ⟨6596998620977166444114965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397999080651444296076643 6596998620977166444114965)
                  ·
                    refine ⟨309234310358304677067889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6596998620977166444114965 309234310358304677067889)
                    ·
                      rfl

theorem cell23_1806695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_1806695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806695 prefixEnd_1806695 := by exact prefixLift 1806695
  have htrace : WordTrace (prefixWord ++ tailWord_1806695) baseStart_1806695 baseEnd_1806695 := by
    simpa [prefixWord, tailWord_1806695, baseEnd_1806695] using wordTrace_append hprefix tailTrace_1806695
  have hstable : (prefixWord ++ tailWord_1806695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806695).length < 2 ^ (prefixWord ++ tailWord_1806695).sum := by decide
  have hdescent : baseEnd_1806695 < baseStart_1806695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806745 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 3, 3, 2]
def baseStart_1806745 : Nat := 118140960795 + 1806745 * 2 ^ 59
def prefixEnd_1806745 : Nat := 4983230072969 + 3 ^ 40 * 1806745 * 2
def baseEnd_1806745 : Nat := 927728605107638835578437

theorem tailTrace_1806745 : CollatzResearch.WordTrace tailWord_1806745 prefixEnd_1806745 927728605107638835578437 := by
  unfold tailWord_1806745
  simp only [CollatzResearch.WordTrace]
  refine ⟨65897403839478907324797689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43931602559652604883198459 65897403839478907324797689)
  ·
    refine ⟨49423052879609180493598267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65897403839478907324797689 49423052879609180493598267)
    ·
      refine ⟨74134579319413770740397401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49423052879609180493598267 74134579319413770740397401)
      ·
        refine ⟨55600934489560328055298051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74134579319413770740397401 55600934489560328055298051)
        ·
          refine ⟨83401401734340492082947077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55600934489560328055298051 83401401734340492082947077)
          ·
            refine ⟨15637762825188842265552577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83401401734340492082947077 15637762825188842265552577)
            ·
              refine ⟨11728322118891631699164433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15637762825188842265552577 11728322118891631699164433)
              ·
                refine ⟨8796241589168723774373325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11728322118891631699164433 8796241589168723774373325)
                ·
                  refine ⟨3298590595938271415389997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8796241589168723774373325 3298590595938271415389997)
                  ·
                    refine ⟨1236971473476851780771249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298590595938271415389997 1236971473476851780771249)
                    ·
                      refine ⟨927728605107638835578437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1236971473476851780771249 927728605107638835578437)
                      ·
                        rfl

theorem cell23_1806745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_1806745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806745 prefixEnd_1806745 := by exact prefixLift 1806745
  have htrace : WordTrace (prefixWord ++ tailWord_1806745) baseStart_1806745 baseEnd_1806745 := by
    simpa [prefixWord, tailWord_1806745, baseEnd_1806745] using wordTrace_append hprefix tailTrace_1806745
  have hstable : (prefixWord ++ tailWord_1806745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806745).length < 2 ^ (prefixWord ++ tailWord_1806745).sum := by decide
  have hdescent : baseEnd_1806745 < baseStart_1806745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806752 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 2, 1, 3]
def baseStart_1806752 : Nat := 118140960795 + 1806752 * 2 ^ 59
def prefixEnd_1806752 : Nat := 4983230072969 + 3 ^ 40 * 1806752 * 2
def baseEnd_1806752 : Nat := 927732199472220308190905

theorem tailTrace_1806752 : CollatzResearch.WordTrace tailWord_1806752 prefixEnd_1806752 927732199472220308190905 := by
  unfold tailWord_1806752
  simp only [CollatzResearch.WordTrace]
  refine ⟨32948829575226773760151255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43931772766969031680201673 32948829575226773760151255)
  ·
    refine ⟨49423244362840160640226883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32948829575226773760151255 49423244362840160640226883)
    ·
      refine ⟨74134866544260240960340325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49423244362840160640226883 74134866544260240960340325)
      ·
        refine ⟨13900287477048795180063811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74134866544260240960340325 13900287477048795180063811)
        ·
          refine ⟨20850431215573192770095717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13900287477048795180063811 20850431215573192770095717)
          ·
            refine ⟨3909455852919973644392947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20850431215573192770095717 3909455852919973644392947)
            ·
              refine ⟨5864183779379960466589421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909455852919973644392947 5864183779379960466589421)
              ·
                refine ⟨2199068917267485174971033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5864183779379960466589421 2199068917267485174971033)
                ·
                  refine ⟨1649301687950613881228275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2199068917267485174971033 1649301687950613881228275)
                  ·
                    refine ⟨2473952531925920821842413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1649301687950613881228275 2473952531925920821842413)
                    ·
                      refine ⟨927732199472220308190905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473952531925920821842413 927732199472220308190905)
                      ·
                        rfl

theorem cell23_1806752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_1806752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806752 prefixEnd_1806752 := by exact prefixLift 1806752
  have htrace : WordTrace (prefixWord ++ tailWord_1806752) baseStart_1806752 baseEnd_1806752 := by
    simpa [prefixWord, tailWord_1806752, baseEnd_1806752] using wordTrace_append hprefix tailTrace_1806752
  have hstable : (prefixWord ++ tailWord_1806752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806752).length < 2 ^ (prefixWord ++ tailWord_1806752).sum := by decide
  have hdescent : baseEnd_1806752 < baseStart_1806752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806775 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 3, 4, 2]
def baseStart_1806775 : Nat := 118140960795 + 1806775 * 2 ^ 59
def prefixEnd_1806775 : Nat := 4983230072969 + 3 ^ 40 * 1806775 * 2
def baseEnd_1806775 : Nat := 927744009527273718203299

theorem tailTrace_1806775 : CollatzResearch.WordTrace tailWord_1806775 prefixEnd_1806775 927744009527273718203299 := by
  unfold tailWord_1806775
  simp only [CollatzResearch.WordTrace]
  refine ⟨65898498029370222448389779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43932332019580148298926519 65898498029370222448389779)
  ·
    refine ⟨98847747044055333672584669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65898498029370222448389779 98847747044055333672584669)
    ·
      refine ⟨37067905141520750127219251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98847747044055333672584669 37067905141520750127219251)
      ·
        refine ⟨55601857712281125190828877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37067905141520750127219251 55601857712281125190828877)
        ·
          refine ⟨20850696642105421946560829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55601857712281125190828877 20850696642105421946560829)
          ·
            refine ⟨7819011240789533229960311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20850696642105421946560829 7819011240789533229960311)
            ·
              refine ⟨11728516861184299844940467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819011240789533229960311 11728516861184299844940467)
              ·
                refine ⟨17592775291776449767410701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11728516861184299844940467 17592775291776449767410701)
                ·
                  refine ⟨6597290734416168662779013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17592775291776449767410701 6597290734416168662779013)
                  ·
                    refine ⟨1236992012703031624271065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6597290734416168662779013 1236992012703031624271065)
                    ·
                      refine ⟨927744009527273718203299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1236992012703031624271065 927744009527273718203299)
                      ·
                        rfl

theorem cell23_1806775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_1806775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806775 prefixEnd_1806775 := by exact prefixLift 1806775
  have htrace : WordTrace (prefixWord ++ tailWord_1806775) baseStart_1806775 baseEnd_1806775 := by
    simpa [prefixWord, tailWord_1806775, baseEnd_1806775] using wordTrace_append hprefix tailTrace_1806775
  have hstable : (prefixWord ++ tailWord_1806775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806775).length < 2 ^ (prefixWord ++ tailWord_1806775).sum := by decide
  have hdescent : baseEnd_1806775 < baseStart_1806775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806778 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_1806778 : Nat := 118140960795 + 1806778 * 2 ^ 59
def prefixEnd_1806778 : Nat := 4983230072969 + 3 ^ 40 * 1806778 * 2
def baseEnd_1806778 : Nat := 927745549969237206465785

theorem tailTrace_1806778 : CollatzResearch.WordTrace tailWord_1806778 prefixEnd_1806778 927745549969237206465785 := by
  unfold tailWord_1806778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16474651862089838490187247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43932404965572902640499325 16474651862089838490187247)
  ·
    refine ⟨24711977793134757735280871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16474651862089838490187247 24711977793134757735280871)
    ·
      refine ⟨37067966689702136602921307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24711977793134757735280871 37067966689702136602921307)
      ·
        refine ⟨55601950034553204904381961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37067966689702136602921307 55601950034553204904381961)
        ·
          refine ⟨41701462525914903678286471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55601950034553204904381961 41701462525914903678286471)
          ·
            refine ⟨62552193788872355517429707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41701462525914903678286471 62552193788872355517429707)
            ·
              refine ⟨93828290683308533276144561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62552193788872355517429707 93828290683308533276144561)
              ·
                refine ⟨70371218012481399957108421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93828290683308533276144561 70371218012481399957108421)
                ·
                  refine ⟨13194603377340262491957829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70371218012481399957108421 13194603377340262491957829)
                  ·
                    refine ⟨2473988133251299217242093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13194603377340262491957829 2473988133251299217242093)
                    ·
                      refine ⟨927745549969237206465785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2473988133251299217242093 927745549969237206465785)
                      ·
                        rfl

theorem cell23_1806778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_1806778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806778 prefixEnd_1806778 := by exact prefixLift 1806778
  have htrace : WordTrace (prefixWord ++ tailWord_1806778) baseStart_1806778 baseEnd_1806778 := by
    simpa [prefixWord, tailWord_1806778, baseEnd_1806778] using wordTrace_append hprefix tailTrace_1806778
  have hstable : (prefixWord ++ tailWord_1806778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806778).length < 2 ^ (prefixWord ++ tailWord_1806778).sum := by decide
  have hdescent : baseEnd_1806778 < baseStart_1806778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806798 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_1806798 : Nat := 118140960795 + 1806798 * 2 ^ 59
def prefixEnd_1806798 : Nat := 4983230072969 + 3 ^ 40 * 1806798 * 2
def baseEnd_1806798 : Nat := 103083979953591903135077

theorem tailTrace_1806798 : CollatzResearch.WordTrace tailWord_1806798 prefixEnd_1806798 103083979953591903135077 := by
  unfold tailWord_1806798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8237417113535862172059631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43932891272191264917651365 8237417113535862172059631)
  ·
    refine ⟨12356125670303793258089447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8237417113535862172059631 12356125670303793258089447)
    ·
      refine ⟨18534188505455689887134171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12356125670303793258089447 18534188505455689887134171)
      ·
        refine ⟨27801282758183534830701257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18534188505455689887134171 27801282758183534830701257)
        ·
          refine ⟨20850962068637651123025943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27801282758183534830701257 20850962068637651123025943)
          ·
            refine ⟨31276443102956476684538915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20850962068637651123025943 31276443102956476684538915)
            ·
              refine ⟨46914664654434715026808373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31276443102956476684538915 46914664654434715026808373)
              ·
                refine ⟨4398249811353254533763285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46914664654434715026808373 4398249811353254533763285)
                ·
                  refine ⟨103083979953591903135077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4398249811353254533763285 103083979953591903135077)
                  ·
                    rfl

theorem cell23_1806798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_1806798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806798 prefixEnd_1806798 := by exact prefixLift 1806798
  have htrace : WordTrace (prefixWord ++ tailWord_1806798) baseStart_1806798 baseEnd_1806798 := by
    simpa [prefixWord, tailWord_1806798, baseEnd_1806798] using wordTrace_append hprefix tailTrace_1806798
  have hstable : (prefixWord ++ tailWord_1806798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806798).length < 2 ^ (prefixWord ++ tailWord_1806798).sum := by decide
  have hdescent : baseEnd_1806798 < baseStart_1806798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806802 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1806802 : Nat := 118140960795 + 1806802 * 2 ^ 59
def prefixEnd_1806802 : Nat := 4983230072969 + 3 ^ 40 * 1806802 * 2
def baseEnd_1806802 : Nat := 309252624501648370855225

theorem tailTrace_1806802 : CollatzResearch.WordTrace tailWord_1806802 prefixEnd_1806802 309252624501648370855225 := by
  unfold tailWord_1806802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16474870700068101514905665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43932988533514937373081773 16474870700068101514905665)
  ·
    refine ⟨12356153025051076136179249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16474870700068101514905665 12356153025051076136179249)
    ·
      refine ⟨9267114768788307102134437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12356153025051076136179249 9267114768788307102134437)
      ·
        refine ⟨1737584019147807581650207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9267114768788307102134437 1737584019147807581650207)
        ·
          refine ⟨2606376028721711372475311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737584019147807581650207 2606376028721711372475311)
          ·
            refine ⟨3909564043082567058712967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606376028721711372475311 3909564043082567058712967)
            ·
              refine ⟨5864346064623850588069451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909564043082567058712967 5864346064623850588069451)
              ·
                refine ⟨8796519096935775882104177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864346064623850588069451 8796519096935775882104177)
                ·
                  refine ⟨6597389322701831911578133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8796519096935775882104177 6597389322701831911578133)
                  ·
                    refine ⟨309252624501648370855225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6597389322701831911578133 309252624501648370855225)
                    ·
                      rfl

theorem cell23_1806802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1806802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806802 prefixEnd_1806802 := by exact prefixLift 1806802
  have htrace : WordTrace (prefixWord ++ tailWord_1806802) baseStart_1806802 baseEnd_1806802 := by
    simpa [prefixWord, tailWord_1806802, baseEnd_1806802] using wordTrace_append hprefix tailTrace_1806802
  have hstable : (prefixWord ++ tailWord_1806802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806802).length < 2 ^ (prefixWord ++ tailWord_1806802).sum := by decide
  have hdescent : baseEnd_1806802 < baseStart_1806802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806805 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1806805 : Nat := 118140960795 + 1806805 * 2 ^ 59
def prefixEnd_1806805 : Nat := 4983230072969 + 3 ^ 40 * 1806805 * 2
def baseEnd_1806805 : Nat := 927759413946908600828161

theorem tailTrace_1806805 : CollatzResearch.WordTrace tailWord_1806805 prefixEnd_1806805 927759413946908600828161 := by
  unfold tailWord_1806805
  simp only [CollatzResearch.WordTrace]
  refine ⟨65899592219261537571981869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43933061479507691714654579 65899592219261537571981869)
  ·
    refine ⟨24712347082223076589493201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65899592219261537571981869 24712347082223076589493201)
    ·
      refine ⟨18534260311667307442119901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24712347082223076589493201 18534260311667307442119901)
      ·
        refine ⟨6950347616875240290794963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18534260311667307442119901 6950347616875240290794963)
        ·
          refine ⟨10425521425312860436192445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950347616875240290794963 10425521425312860436192445)
          ·
            refine ⟨3909570534492322663572167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10425521425312860436192445 3909570534492322663572167)
            ·
              refine ⟨5864355801738483995358251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909570534492322663572167 5864355801738483995358251)
              ·
                refine ⟨8796533702607725993037377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864355801738483995358251 8796533702607725993037377)
                ·
                  refine ⟨6597400276955794494778033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8796533702607725993037377 6597400276955794494778033)
                  ·
                    refine ⟨4948050207716845871083525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6597400276955794494778033 4948050207716845871083525)
                    ·
                      refine ⟨927759413946908600828161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4948050207716845871083525 927759413946908600828161)
                      ·
                        rfl

theorem cell23_1806805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1806805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806805 prefixEnd_1806805 := by exact prefixLift 1806805
  have htrace : WordTrace (prefixWord ++ tailWord_1806805) baseStart_1806805 baseEnd_1806805 := by
    simpa [prefixWord, tailWord_1806805, baseEnd_1806805] using wordTrace_append hprefix tailTrace_1806805
  have hstable : (prefixWord ++ tailWord_1806805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806805).length < 2 ^ (prefixWord ++ tailWord_1806805).sum := by decide
  have hdescent : baseEnd_1806805 < baseStart_1806805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806828 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_1806828 : Nat := 118140960795 + 1806828 * 2 ^ 59
def prefixEnd_1806828 : Nat := 4983230072969 + 3 ^ 40 * 1806828 * 2
def baseEnd_1806828 : Nat := 309257074667320670280185

theorem tailTrace_1806828 : CollatzResearch.WordTrace tailWord_1806828 prefixEnd_1806828 309257074667320670280185 := by
  unfold tailWord_1806828
  simp only [CollatzResearch.WordTrace]
  refine ⟨32950215549089106250034569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43933620732118808333379425 32950215549089106250034569)
  ·
    refine ⟨24712661661816829687525927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32950215549089106250034569 24712661661816829687525927)
    ·
      refine ⟨37068992492725244531288891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24712661661816829687525927 37068992492725244531288891)
      ·
        refine ⟨55603488739087866796933337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37068992492725244531288891 55603488739087866796933337)
        ·
          refine ⟨41702616554315900097700003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55603488739087866796933337 41702616554315900097700003)
          ·
            refine ⟨62553924831473850146550005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41702616554315900097700003 62553924831473850146550005)
            ·
              refine ⟨5864430452950673451239063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62553924831473850146550005 5864430452950673451239063)
              ·
                refine ⟨8796645679426010176858595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864430452950673451239063 8796645679426010176858595)
                ·
                  refine ⟨13194968519139015265287893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8796645679426010176858595 13194968519139015265287893)
                  ·
                    refine ⟨309257074667320670280185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13194968519139015265287893 309257074667320670280185)
                    ·
                      rfl

theorem cell23_1806828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_1806828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806828 prefixEnd_1806828 := by exact prefixLift 1806828
  have htrace : WordTrace (prefixWord ++ tailWord_1806828) baseStart_1806828 baseEnd_1806828 := by
    simpa [prefixWord, tailWord_1806828, baseEnd_1806828] using wordTrace_append hprefix tailTrace_1806828
  have hstable : (prefixWord ++ tailWord_1806828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806828).length < 2 ^ (prefixWord ++ tailWord_1806828).sum := by decide
  have hdescent : baseEnd_1806828 < baseStart_1806828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806865 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 1, 6, 2]
def baseStart_1806865 : Nat := 118140960795 + 1806865 * 2 ^ 59
def prefixEnd_1806865 : Nat := 4983230072969 + 3 ^ 40 * 1806865 * 2
def baseEnd_1806865 : Nat := 927790222786178366077885

theorem tailTrace_1806865 : CollatzResearch.WordTrace tailWord_1806865 prefixEnd_1806865 927790222786178366077885 := by
  unfold tailWord_1806865
  simp only [CollatzResearch.WordTrace]
  refine ⟨65901780599044167819166049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43934520399362778546110699 65901780599044167819166049)
  ·
    refine ⟨49426335449283125864374537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65901780599044167819166049 49426335449283125864374537)
    ·
      refine ⟨37069751586962344398280903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49426335449283125864374537 37069751586962344398280903)
      ·
        refine ⟨55604627380443516597421355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37069751586962344398280903 55604627380443516597421355)
        ·
          refine ⟨83406941070665274896132033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55604627380443516597421355 83406941070665274896132033)
          ·
            refine ⟨62555205802998956172099025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83406941070665274896132033 62555205802998956172099025)
            ·
              refine ⟨46916404352249217129074269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62555205802998956172099025 46916404352249217129074269)
              ·
                refine ⟨17593651632093456423402851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46916404352249217129074269 17593651632093456423402851)
                ·
                  refine ⟨26390477448140184635104277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17593651632093456423402851 26390477448140184635104277)
                  ·
                    refine ⟨1237053630381571154770513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26390477448140184635104277 1237053630381571154770513)
                    ·
                      refine ⟨927790222786178366077885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1237053630381571154770513 927790222786178366077885)
                      ·
                        rfl

theorem cell23_1806865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_1806865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806865 prefixEnd_1806865 := by exact prefixLift 1806865
  have htrace : WordTrace (prefixWord ++ tailWord_1806865) baseStart_1806865 baseEnd_1806865 := by
    simpa [prefixWord, tailWord_1806865, baseEnd_1806865] using wordTrace_append hprefix tailTrace_1806865
  have hstable : (prefixWord ++ tailWord_1806865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806865).length < 2 ^ (prefixWord ++ tailWord_1806865).sum := by decide
  have hdescent : baseEnd_1806865 < baseStart_1806865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806885 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_1806885 : Nat := 118140960795 + 1806885 * 2 ^ 59
def prefixEnd_1806885 : Nat := 4983230072969 + 3 ^ 40 * 1806885 * 2
def baseEnd_1806885 : Nat := 927800492399268287827793

theorem tailTrace_1806885 : CollatzResearch.WordTrace tailWord_1806885 prefixEnd_1806885 927800492399268287827793 := by
  unfold tailWord_1806885
  simp only [CollatzResearch.WordTrace]
  refine ⟨65902510058971711234894109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43935006705981140823262739 65902510058971711234894109)
  ·
    refine ⟨24713441272114391713085291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65902510058971711234894109 24713441272114391713085291)
    ·
      refine ⟨37070161908171587569627937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24713441272114391713085291 37070161908171587569627937)
      ·
        refine ⟨27802621431128690677220953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37070161908171587569627937 27802621431128690677220953)
        ·
          refine ⟨20851966073346518007915715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27802621431128690677220953 20851966073346518007915715)
          ·
            refine ⟨31277949110019777011873573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20851966073346518007915715 31277949110019777011873573)
            ·
              refine ⟨5864615458128708189726295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31277949110019777011873573 5864615458128708189726295)
              ·
                refine ⟨8796923187193062284589443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864615458128708189726295 8796923187193062284589443)
                ·
                  refine ⟨13195384780789593426884165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8796923187193062284589443 13195384780789593426884165)
                  ·
                    refine ⟨2474134646398048767540781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13195384780789593426884165 2474134646398048767540781)
                    ·
                      refine ⟨927800492399268287827793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2474134646398048767540781 927800492399268287827793)
                      ·
                        rfl

theorem cell23_1806885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_1806885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806885 prefixEnd_1806885 := by exact prefixLift 1806885
  have htrace : WordTrace (prefixWord ++ tailWord_1806885) baseStart_1806885 baseEnd_1806885 := by
    simpa [prefixWord, tailWord_1806885, baseEnd_1806885] using wordTrace_append hprefix tailTrace_1806885
  have hstable : (prefixWord ++ tailWord_1806885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806885).length < 2 ^ (prefixWord ++ tailWord_1806885).sum := by decide
  have hdescent : baseEnd_1806885 < baseStart_1806885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806905 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 6]
def baseStart_1806905 : Nat := 118140960795 + 1806905 * 2 ^ 59
def prefixEnd_1806905 : Nat := 4983230072969 + 3 ^ 40 * 1806905 * 2
def baseEnd_1806905 : Nat := 103090084668039801064189

theorem tailTrace_1806905 : CollatzResearch.WordTrace tailWord_1806905 prefixEnd_1806905 103090084668039801064189 := by
  unfold tailWord_1806905
  simp only [CollatzResearch.WordTrace]
  refine ⟨65903239518899254650622169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43935493012599503100414779 65903239518899254650622169)
  ·
    refine ⟨49427429639174440987966627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65903239518899254650622169 49427429639174440987966627)
    ·
      refine ⟨74141144458761661481949941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49427429639174440987966627 74141144458761661481949941)
      ·
        refine ⟨6950732293008905763932807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74141144458761661481949941 6950732293008905763932807)
        ·
          refine ⟨10426098439513358645899211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950732293008905763932807 10426098439513358645899211)
          ·
            refine ⟨15639147659270037968848817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426098439513358645899211 15639147659270037968848817)
            ·
              refine ⟨11729360744452528476636613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15639147659270037968848817 11729360744452528476636613)
              ·
                refine ⟨2199255139584849089369365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11729360744452528476636613 2199255139584849089369365)
                ·
                  refine ⟨103090084668039801064189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2199255139584849089369365 103090084668039801064189)
                  ·
                    rfl

theorem cell23_1806905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 6].length) (baseStart_1806905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806905 prefixEnd_1806905 := by exact prefixLift 1806905
  have htrace : WordTrace (prefixWord ++ tailWord_1806905) baseStart_1806905 baseEnd_1806905 := by
    simpa [prefixWord, tailWord_1806905, baseEnd_1806905] using wordTrace_append hprefix tailTrace_1806905
  have hstable : (prefixWord ++ tailWord_1806905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806905).length < 2 ^ (prefixWord ++ tailWord_1806905).sum := by decide
  have hdescent : baseEnd_1806905 < baseStart_1806905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806909 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_1806909 : Nat := 118140960795 + 1806909 * 2 ^ 59
def prefixEnd_1806909 : Nat := 4983230072969 + 3 ^ 40 * 1806909 * 2
def baseEnd_1806909 : Nat := 309270938644992064642561

theorem tailTrace_1806909 : CollatzResearch.WordTrace tailWord_1806909 prefixEnd_1806909 309270938644992064642561 := by
  unfold tailWord_1806909
  simp only [CollatzResearch.WordTrace]
  refine ⟨65903385410884763333767781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43935590273923175555845187 65903385410884763333767781)
  ·
    refine ⟨12356884764540893125081459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65903385410884763333767781 12356884764540893125081459)
    ·
      refine ⟨18535327146811339687622189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12356884764540893125081459 18535327146811339687622189)
      ·
        refine ⟨6950747680054252382858321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18535327146811339687622189 6950747680054252382858321)
        ·
          refine ⟨5213060760040689287143741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6950747680054252382858321 5213060760040689287143741)
          ·
            refine ⟨1954897785015258482678903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5213060760040689287143741 1954897785015258482678903)
            ·
              refine ⟨2932346677522887724018355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954897785015258482678903 2932346677522887724018355)
              ·
                refine ⟨4398520016284331586027533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932346677522887724018355 4398520016284331586027533)
                ·
                  refine ⟨1649445006106624344760325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4398520016284331586027533 1649445006106624344760325)
                  ·
                    refine ⟨309270938644992064642561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1649445006106624344760325 309270938644992064642561)
                    ·
                      rfl

theorem cell23_1806909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_1806909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806909 prefixEnd_1806909 := by exact prefixLift 1806909
  have htrace : WordTrace (prefixWord ++ tailWord_1806909) baseStart_1806909 baseEnd_1806909 := by
    simpa [prefixWord, tailWord_1806909, baseEnd_1806909] using wordTrace_append hprefix tailTrace_1806909
  have hstable : (prefixWord ++ tailWord_1806909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806909).length < 2 ^ (prefixWord ++ tailWord_1806909).sum := by decide
  have hdescent : baseEnd_1806909 < baseStart_1806909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806922 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 6]
def baseStart_1806922 : Nat := 118140960795 + 1806922 * 2 ^ 59
def prefixEnd_1806922 : Nat := 4983230072969 + 3 ^ 40 * 1806922 * 2
def baseEnd_1806922 : Nat := 103091054575942738118347

theorem tailTrace_1806922 : CollatzResearch.WordTrace tailWord_1806922 prefixEnd_1806922 103091054575942738118347 := by
  unfold tailWord_1806922
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475964889959416638497755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43935906373225111035994013 16475964889959416638497755)
  ·
    refine ⟨24713947334939124957746633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16475964889959416638497755 24713947334939124957746633)
    ·
      refine ⟨18535460501204343718309975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24713947334939124957746633 18535460501204343718309975)
      ·
        refine ⟨27803190751806515577464963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18535460501204343718309975 27803190751806515577464963)
        ·
          refine ⟨41704786127709773366197445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27803190751806515577464963 41704786127709773366197445)
          ·
            refine ⟨7819647398945582506162021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41704786127709773366197445 7819647398945582506162021)
            ·
              refine ⟨1466183887302296719905379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7819647398945582506162021 1466183887302296719905379)
              ·
                refine ⟨2199275830953445079858069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466183887302296719905379 2199275830953445079858069)
                ·
                  refine ⟨103091054575942738118347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2199275830953445079858069 103091054575942738118347)
                  ·
                    rfl

theorem cell23_1806922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_1806922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806922 prefixEnd_1806922 := by exact prefixLift 1806922
  have htrace : WordTrace (prefixWord ++ tailWord_1806922) baseStart_1806922 baseEnd_1806922 := by
    simpa [prefixWord, tailWord_1806922, baseEnd_1806922] using wordTrace_append hprefix tailTrace_1806922
  have hstable : (prefixWord ++ tailWord_1806922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806922).length < 2 ^ (prefixWord ++ tailWord_1806922).sum := by decide
  have hdescent : baseEnd_1806922 < baseStart_1806922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806928 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_1806928 : Nat := 118140960795 + 1806928 * 2 ^ 59
def prefixEnd_1806928 : Nat := 4983230072969 + 3 ^ 40 * 1806928 * 2
def baseEnd_1806928 : Nat := 927822572067411619590095

theorem tailTrace_1806928 : CollatzResearch.WordTrace tailWord_1806928 prefixEnd_1806928 927822572067411619590095 := by
  unfold tailWord_1806928
  simp only [CollatzResearch.WordTrace]
  refine ⟨32952039198907964789354719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43936052265210619719139625 32952039198907964789354719)
  ·
    refine ⟨49428058798361947184032079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32952039198907964789354719 49428058798361947184032079)
    ·
      refine ⟨74142088197542920776048119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49428058798361947184032079 74142088197542920776048119)
      ·
        refine ⟨111213132296314381164072179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74142088197542920776048119 111213132296314381164072179)
        ·
          refine ⟨166819698444471571746108269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111213132296314381164072179 166819698444471571746108269)
          ·
            refine ⟨62557386916676839404790601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166819698444471571746108269 62557386916676839404790601)
            ·
              refine ⟨46918040187507629553592951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62557386916676839404790601 46918040187507629553592951)
              ·
                refine ⟨70377060281261444330389427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46918040187507629553592951 70377060281261444330389427)
                ·
                  refine ⟨105565590421892166495584141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70377060281261444330389427 105565590421892166495584141)
                  ·
                    refine ⟨39587096408209562435844053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105565590421892166495584141 39587096408209562435844053)
                    ·
                      refine ⟨927822572067411619590095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39587096408209562435844053 927822572067411619590095)
                      ·
                        rfl

theorem cell23_1806928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_1806928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806928 prefixEnd_1806928 := by exact prefixLift 1806928
  have htrace : WordTrace (prefixWord ++ tailWord_1806928) baseStart_1806928 baseEnd_1806928 := by
    simpa [prefixWord, tailWord_1806928, baseEnd_1806928] using wordTrace_append hprefix tailTrace_1806928
  have hstable : (prefixWord ++ tailWord_1806928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806928).length < 2 ^ (prefixWord ++ tailWord_1806928).sum := by decide
  have hdescent : baseEnd_1806928 < baseStart_1806928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1806935 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 3, 5]
def baseStart_1806935 : Nat := 118140960795 + 1806935 * 2 ^ 59
def prefixEnd_1806935 : Nat := 4983230072969 + 3 ^ 40 * 1806935 * 2
def baseEnd_1806935 : Nat := 309275388810664364067521

theorem tailTrace_1806935 : CollatzResearch.WordTrace tailWord_1806935 prefixEnd_1806935 309275388810664364067521 := by
  unfold tailWord_1806935
  simp only [CollatzResearch.WordTrace]
  refine ⟨65904333708790569774214259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43936222472527046516142839 65904333708790569774214259)
  ·
    refine ⟨98856500563185854661321389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65904333708790569774214259 98856500563185854661321389)
    ·
      refine ⟨37071187711194695497995521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98856500563185854661321389 37071187711194695497995521)
      ·
        refine ⟨27803390783396021623496641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37071187711194695497995521 27803390783396021623496641)
        ·
          refine ⟨20852543087547016217622481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27803390783396021623496641 20852543087547016217622481)
          ·
            refine ⟨15639407315660262163216861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20852543087547016217622481 15639407315660262163216861)
            ·
              refine ⟨5864777743372598311206323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15639407315660262163216861 5864777743372598311206323)
              ·
                refine ⟨8797166615058897466809485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864777743372598311206323 8797166615058897466809485)
                ·
                  refine ⟨3298937480647086550053557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8797166615058897466809485 3298937480647086550053557)
                  ·
                    refine ⟨309275388810664364067521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3298937480647086550053557 309275388810664364067521)
                    ·
                      rfl

theorem cell23_1806935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_1806935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1806935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1806935 prefixEnd_1806935 := by exact prefixLift 1806935
  have htrace : WordTrace (prefixWord ++ tailWord_1806935) baseStart_1806935 baseEnd_1806935 := by
    simpa [prefixWord, tailWord_1806935, baseEnd_1806935] using wordTrace_append hprefix tailTrace_1806935
  have hstable : (prefixWord ++ tailWord_1806935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1806935).length < 2 ^ (prefixWord ++ tailWord_1806935).sum := by decide
  have hdescent : baseEnd_1806935 < baseStart_1806935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1806935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807006 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_1807006 : Nat := 118140960795 + 1807006 * 2 ^ 59
def prefixEnd_1807006 : Nat := 4983230072969 + 3 ^ 40 * 1807006 * 2
def baseEnd_1807006 : Nat := 927862623558462314414737

theorem tailTrace_1807006 : CollatzResearch.WordTrace tailWord_1807006 prefixEnd_1807006 927862623558462314414737 := by
  unfold tailWord_1807006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8238365411441668612506109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43937948861022232600032581 8238365411441668612506109)
  ·
    refine ⟨3089387029290625729689791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8238365411441668612506109 3089387029290625729689791)
    ·
      refine ⟨4634080543935938594534687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3089387029290625729689791 4634080543935938594534687)
      ·
        refine ⟨6951120815903907891802031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634080543935938594534687 6951120815903907891802031)
        ·
          refine ⟨10426681223855861837703047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951120815903907891802031 10426681223855861837703047)
          ·
            refine ⟨15640021835783792756554571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426681223855861837703047 15640021835783792756554571)
            ·
              refine ⟨23460032753675689134831857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15640021835783792756554571 23460032753675689134831857)
              ·
                refine ⟨17595024565256766851123893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23460032753675689134831857 17595024565256766851123893)
                ·
                  refine ⟨1649533552992821892292865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17595024565256766851123893 1649533552992821892292865)
                  ·
                    refine ⟨1237150164744616419219649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1649533552992821892292865 1237150164744616419219649)
                    ·
                      refine ⟨927862623558462314414737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1237150164744616419219649 927862623558462314414737)
                      ·
                        rfl

theorem cell23_1807006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_1807006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807006 prefixEnd_1807006 := by exact prefixLift 1807006
  have htrace : WordTrace (prefixWord ++ tailWord_1807006) baseStart_1807006 baseEnd_1807006 := by
    simpa [prefixWord, tailWord_1807006, baseEnd_1807006] using wordTrace_append hprefix tailTrace_1807006
  have hstable : (prefixWord ++ tailWord_1807006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807006).length < 2 ^ (prefixWord ++ tailWord_1807006).sum := by decide
  have hdescent : baseEnd_1807006 < baseStart_1807006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807039 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 3]
def baseStart_1807039 : Nat := 118140960795 + 1807039 * 2 ^ 59
def prefixEnd_1807039 : Nat := 4983230072969 + 3 ^ 40 * 1807039 * 2
def baseEnd_1807039 : Nat := 927879568420060685302085

theorem tailTrace_1807039 : CollatzResearch.WordTrace tailWord_1807039 prefixEnd_1807039 927879568420060685302085 := by
  unfold tailWord_1807039
  simp only [CollatzResearch.WordTrace]
  refine ⟨65908126900413795536000171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43938751266942530357333447 65908126900413795536000171)
  ·
    refine ⟨98862190350620693304000257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65908126900413795536000171 98862190350620693304000257)
    ·
      refine ⟨74146642762965519978000193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98862190350620693304000257 74146642762965519978000193)
      ·
        refine ⟨55609982072224139983500145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74146642762965519978000193 55609982072224139983500145)
        ·
          refine ⟨41707486554168104987625109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55609982072224139983500145 41707486554168104987625109)
          ·
            refine ⟨1955038432226629921294927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41707486554168104987625109 1955038432226629921294927)
            ·
              refine ⟨2932557648339944881942391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955038432226629921294927 2932557648339944881942391)
              ·
                refine ⟨4398836472509917322913587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932557648339944881942391 4398836472509917322913587)
                ·
                  refine ⟨6598254708764875984370381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398836472509917322913587 6598254708764875984370381)
                  ·
                    refine ⟨2474345515786828494138893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6598254708764875984370381 2474345515786828494138893)
                    ·
                      refine ⟨927879568420060685302085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2474345515786828494138893 927879568420060685302085)
                      ·
                        rfl

theorem cell23_1807039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_1807039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807039 prefixEnd_1807039 := by exact prefixLift 1807039
  have htrace : WordTrace (prefixWord ++ tailWord_1807039) baseStart_1807039 baseEnd_1807039 := by
    simpa [prefixWord, tailWord_1807039, baseEnd_1807039] using wordTrace_append hprefix tailTrace_1807039
  have hstable : (prefixWord ++ tailWord_1807039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807039).length < 2 ^ (prefixWord ++ tailWord_1807039).sum := by decide
  have hdescent : baseEnd_1807039 < baseStart_1807039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807046 : List Nat := [6, 1, 2, 1, 2, 1, 1, 9]
def baseStart_1807046 : Nat := 118140960795 + 1807046 * 2 ^ 59
def prefixEnd_1807046 : Nat := 4983230072969 + 3 ^ 40 * 1807046 * 2
def baseEnd_1807046 : Nat := 34366043066097857700539

theorem tailTrace_1807046 : CollatzResearch.WordTrace tailWord_1807046 prefixEnd_1807046 34366043066097857700539 := by
  unfold tailWord_1807046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2059636944105888616609531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43938921474258957154336661 2059636944105888616609531)
  ·
    refine ⟨3089455416158832924914297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2059636944105888616609531 3089455416158832924914297)
    ·
      refine ⟨2317091562119124693685723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3089455416158832924914297 2317091562119124693685723)
      ·
        refine ⟨3475637343178687040528585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2317091562119124693685723 3475637343178687040528585)
        ·
          refine ⟨2606728007384015280396439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3475637343178687040528585 2606728007384015280396439)
          ·
            refine ⟨3910092011076022920594659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606728007384015280396439 3910092011076022920594659)
            ·
              refine ⟨5865138016614034380891989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910092011076022920594659 5865138016614034380891989)
              ·
                refine ⟨34366043066097857700539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5865138016614034380891989 34366043066097857700539)
                ·
                  rfl

theorem cell23_1807046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_1807046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807046 prefixEnd_1807046 := by exact prefixLift 1807046
  have htrace : WordTrace (prefixWord ++ tailWord_1807046) baseStart_1807046 baseEnd_1807046 := by
    simpa [prefixWord, tailWord_1807046, baseEnd_1807046] using wordTrace_append hprefix tailTrace_1807046
  have hstable : (prefixWord ++ tailWord_1807046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807046).length < 2 ^ (prefixWord ++ tailWord_1807046).sum := by decide
  have hdescent : baseEnd_1807046 < baseStart_1807046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807052 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1807052 : Nat := 118140960795 + 1807052 * 2 ^ 59
def prefixEnd_1807052 : Nat := 4983230072969 + 3 ^ 40 * 1807052 * 2
def baseEnd_1807052 : Nat := 927886243668569134439525

theorem tailTrace_1807052 : CollatzResearch.WordTrace tailWord_1807052 prefixEnd_1807052 927886243668569134439525 := by
  unfold tailWord_1807052
  simp only [CollatzResearch.WordTrace]
  refine ⟨32954300524683349378111705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43939067366244465837482273 32954300524683349378111705)
  ·
    refine ⟨24715725393512512033583779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32954300524683349378111705 24715725393512512033583779)
    ·
      refine ⟨37073588090268768050375669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24715725393512512033583779 37073588090268768050375669)
      ·
        refine ⟨3475648883462697004722719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37073588090268768050375669 3475648883462697004722719)
        ·
          refine ⟨5213473325194045507084079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475648883462697004722719 5213473325194045507084079)
          ·
            refine ⟨7820209987791068260626119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213473325194045507084079 7820209987791068260626119)
            ·
              refine ⟨11730314981686602390939179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7820209987791068260626119 11730314981686602390939179)
              ·
                refine ⟨17595472472529903586408769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11730314981686602390939179 17595472472529903586408769)
                ·
                  refine ⟨13196604354397427689806577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17595472472529903586408769 13196604354397427689806577)
                  ·
                    refine ⟨9897453265798070767354933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13196604354397427689806577 9897453265798070767354933)
                    ·
                      refine ⟨927886243668569134439525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9897453265798070767354933 927886243668569134439525)
                      ·
                        rfl

theorem cell23_1807052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1807052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807052 prefixEnd_1807052 := by exact prefixLift 1807052
  have htrace : WordTrace (prefixWord ++ tailWord_1807052) baseStart_1807052 baseEnd_1807052 := by
    simpa [prefixWord, tailWord_1807052, baseEnd_1807052] using wordTrace_append hprefix tailTrace_1807052
  have hstable : (prefixWord ++ tailWord_1807052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807052).length < 2 ^ (prefixWord ++ tailWord_1807052).sum := by decide
  have hdescent : baseEnd_1807052 < baseStart_1807052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807082 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1807082 : Nat := 118140960795 + 1807082 * 2 ^ 59
def prefixEnd_1807082 : Nat := 4983230072969 + 3 ^ 40 * 1807082 * 2
def baseEnd_1807082 : Nat := 927901648088204017064387

theorem tailTrace_1807082 : CollatzResearch.WordTrace tailWord_1807082 prefixEnd_1807082 927901648088204017064387 := by
  unfold tailWord_1807082
  simp only [CollatzResearch.WordTrace]
  refine ⟨16477423809814503469953875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43939796826172009253210333 16477423809814503469953875)
  ·
    refine ⟨24716135714721755204930813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16477423809814503469953875 24716135714721755204930813)
    ·
      refine ⟨9268550893020658201849055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24716135714721755204930813 9268550893020658201849055)
      ·
        refine ⟨13902826339530987302773583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9268550893020658201849055 13902826339530987302773583)
        ·
          refine ⟨20854239509296480954160375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13902826339530987302773583 20854239509296480954160375)
          ·
            refine ⟨31281359263944721431240563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20854239509296480954160375 31281359263944721431240563)
            ·
              refine ⟨46922038895917082146860845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31281359263944721431240563 46922038895917082146860845)
              ·
                refine ⟨17595764585968905805072817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46922038895917082146860845 17595764585968905805072817)
                ·
                  refine ⟨13196823439476679353804613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17595764585968905805072817 13196823439476679353804613)
                  ·
                    refine ⟨2474404394901877378838365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13196823439476679353804613 2474404394901877378838365)
                    ·
                      refine ⟨927901648088204017064387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2474404394901877378838365 927901648088204017064387)
                      ·
                        rfl

theorem cell23_1807082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1807082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807082 prefixEnd_1807082 := by exact prefixLift 1807082
  have htrace : WordTrace (prefixWord ++ tailWord_1807082) baseStart_1807082 baseEnd_1807082 := by
    simpa [prefixWord, tailWord_1807082, baseEnd_1807082] using wordTrace_append hprefix tailTrace_1807082
  have hstable : (prefixWord ++ tailWord_1807082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807082).length < 2 ^ (prefixWord ++ tailWord_1807082).sum := by decide
  have hdescent : baseEnd_1807082 < baseStart_1807082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807096 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 2, 2, 2]
def baseStart_1807096 : Nat := 118140960795 + 1807096 * 2 ^ 59
def prefixEnd_1807096 : Nat := 4983230072969 + 3 ^ 40 * 1807096 * 2
def baseEnd_1807096 : Nat := 927908836817366962289323

theorem tailTrace_1807096 : CollatzResearch.WordTrace tailWord_1807096 prefixEnd_1807096 927908836817366962289323 := by
  unfold tailWord_1807096
  simp only [CollatzResearch.WordTrace]
  refine ⟨32955102930603647135412571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43940137240804862847216761 32955102930603647135412571)
  ·
    refine ⟨49432654395905470703118857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32955102930603647135412571 49432654395905470703118857)
    ·
      refine ⟨37074490796929103027339143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49432654395905470703118857 37074490796929103027339143)
      ·
        refine ⟨55611736195393654541008715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37074490796929103027339143 55611736195393654541008715)
        ·
          refine ⟨83417604293090481811513073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55611736195393654541008715 83417604293090481811513073)
          ·
            refine ⟨62563203219817861358634805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83417604293090481811513073 62563203219817861358634805)
            ·
              refine ⟨5865300301857924502372013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62563203219817861358634805 5865300301857924502372013)
              ·
                refine ⟨2199487613196721688389505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5865300301857924502372013 2199487613196721688389505)
                ·
                  refine ⟨1649615709897541266292129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2199487613196721688389505 1649615709897541266292129)
                  ·
                    refine ⟨1237211782423155949719097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1649615709897541266292129 1237211782423155949719097)
                    ·
                      refine ⟨927908836817366962289323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1237211782423155949719097 927908836817366962289323)
                      ·
                        rfl

theorem cell23_1807096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_1807096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807096 prefixEnd_1807096 := by exact prefixLift 1807096
  have htrace : WordTrace (prefixWord ++ tailWord_1807096) baseStart_1807096 baseEnd_1807096 := by
    simpa [prefixWord, tailWord_1807096, baseEnd_1807096] using wordTrace_append hprefix tailTrace_1807096
  have hstable : (prefixWord ++ tailWord_1807096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807096).length < 2 ^ (prefixWord ++ tailWord_1807096).sum := by decide
  have hdescent : baseEnd_1807096 < baseStart_1807096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807136 : List Nat := [2, 1, 1, 5, 1, 2, 4, 2, 5]
def baseStart_1807136 : Nat := 118140960795 + 1807136 * 2 ^ 59
def prefixEnd_1807136 : Nat := 4983230072969 + 3 ^ 40 * 1807136 * 2
def baseEnd_1807136 : Nat := 103103264004838533976571

theorem tailTrace_1807136 : CollatzResearch.WordTrace tailWord_1807136 prefixEnd_1807136 103103264004838533976571 := by
  unfold tailWord_1807136
  simp only [CollatzResearch.WordTrace]
  refine ⟨32955832390531190551140631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43941109854041587401520841 32955832390531190551140631)
  ·
    refine ⟨49433748585796785826710947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32955832390531190551140631 49433748585796785826710947)
    ·
      refine ⟨74150622878695178740066421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49433748585796785826710947 74150622878695178740066421)
      ·
        refine ⟨6951620894877673006881227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74150622878695178740066421 6951620894877673006881227)
        ·
          refine ⟨10427431342316509510321841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951620894877673006881227 10427431342316509510321841)
          ·
            refine ⟨7820573506737382132741381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10427431342316509510321841 7820573506737382132741381)
            ·
              refine ⟨1466357532513259149889009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7820573506737382132741381 1466357532513259149889009)
              ·
                refine ⟨1099768149384944362416757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466357532513259149889009 1099768149384944362416757)
                ·
                  refine ⟨103103264004838533976571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1099768149384944362416757 103103264004838533976571)
                  ·
                    rfl

theorem cell23_1807136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 5].length) (baseStart_1807136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807136 prefixEnd_1807136 := by exact prefixLift 1807136
  have htrace : WordTrace (prefixWord ++ tailWord_1807136) baseStart_1807136 baseEnd_1807136 := by
    simpa [prefixWord, tailWord_1807136, baseEnd_1807136] using wordTrace_append hprefix tailTrace_1807136
  have hstable : (prefixWord ++ tailWord_1807136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807136).length < 2 ^ (prefixWord ++ tailWord_1807136).sum := by decide
  have hdescent : baseEnd_1807136 < baseStart_1807136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807152 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_1807152 : Nat := 118140960795 + 1807152 * 2 ^ 59
def prefixEnd_1807152 : Nat := 4983230072969 + 3 ^ 40 * 1807152 * 2
def baseEnd_1807152 : Nat := 927937591734018743189065

theorem tailTrace_1807152 : CollatzResearch.WordTrace tailWord_1807152 prefixEnd_1807152 927937591734018743189065 := by
  unfold tailWord_1807152
  simp only [CollatzResearch.WordTrace]
  refine ⟨32956124174502207917431855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43941498899336277223242473 32956124174502207917431855)
  ·
    refine ⟨49434186261753311876147783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32956124174502207917431855 49434186261753311876147783)
    ·
      refine ⟨74151279392629967814221675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49434186261753311876147783 74151279392629967814221675)
      ·
        refine ⟨111226919088944951721332513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74151279392629967814221675 111226919088944951721332513)
        ·
          refine ⟨83420189316708713790999385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111226919088944951721332513 83420189316708713790999385)
          ·
            refine ⟨62565141987531535343249539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83420189316708713790999385 62565141987531535343249539)
            ·
              refine ⟨93847712981297303014874309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62565141987531535343249539 93847712981297303014874309)
              ·
                refine ⟨17596446183993244315288933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93847712981297303014874309 17596446183993244315288933)
                ·
                  refine ⟨3299333659498733309116675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17596446183993244315288933 3299333659498733309116675)
                  ·
                    refine ⟨4949000489248099963675013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3299333659498733309116675 4949000489248099963675013)
                    ·
                      refine ⟨927937591734018743189065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4949000489248099963675013 927937591734018743189065)
                      ·
                        rfl

theorem cell23_1807152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_1807152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807152 prefixEnd_1807152 := by exact prefixLift 1807152
  have htrace : WordTrace (prefixWord ++ tailWord_1807152) baseStart_1807152 baseEnd_1807152 := by
    simpa [prefixWord, tailWord_1807152, baseEnd_1807152] using wordTrace_append hprefix tailTrace_1807152
  have hstable : (prefixWord ++ tailWord_1807152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807152).length < 2 ^ (prefixWord ++ tailWord_1807152).sum := by decide
  have hdescent : baseEnd_1807152 < baseStart_1807152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807182 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1807182 : Nat := 118140960795 + 1807182 * 2 ^ 59
def prefixEnd_1807182 : Nat := 4983230072969 + 3 ^ 40 * 1807182 * 2
def baseEnd_1807182 : Nat := 927952996153653625813927

theorem tailTrace_1807182 : CollatzResearch.WordTrace tailWord_1807182 prefixEnd_1807182 927952996153653625813927 := by
  unfold tailWord_1807182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239167817361966369806975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43942228359263820638970533 8239167817361966369806975)
  ·
    refine ⟨12358751726042949554710463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8239167817361966369806975 12358751726042949554710463)
    ·
      refine ⟨18538127589064424332065695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12358751726042949554710463 18538127589064424332065695)
      ·
        refine ⟨27807191383596636498098543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18538127589064424332065695 27807191383596636498098543)
        ·
          refine ⟨41710787075394954747147815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27807191383596636498098543 41710787075394954747147815)
          ·
            refine ⟨62566180613092432120721723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41710787075394954747147815 62566180613092432120721723)
            ·
              refine ⟨93849270919638648181082585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62566180613092432120721723 93849270919638648181082585)
              ·
                refine ⟨70386953189728986135811939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93849270919638648181082585 70386953189728986135811939)
                ·
                  refine ⟨105580429784593479203717909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70386953189728986135811939 105580429784593479203717909)
                  ·
                    refine ⟨4949082646152819337674277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105580429784593479203717909 4949082646152819337674277)
                    ·
                      refine ⟨927952996153653625813927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4949082646152819337674277 927952996153653625813927)
                      ·
                        rfl

theorem cell23_1807182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1807182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807182 prefixEnd_1807182 := by exact prefixLift 1807182
  have htrace : WordTrace (prefixWord ++ tailWord_1807182) baseStart_1807182 baseEnd_1807182 := by
    simpa [prefixWord, tailWord_1807182, baseEnd_1807182] using wordTrace_append hprefix tailTrace_1807182
  have hstable : (prefixWord ++ tailWord_1807182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807182).length < 2 ^ (prefixWord ++ tailWord_1807182).sum := by decide
  have hdescent : baseEnd_1807182 < baseStart_1807182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807189 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1807189 : Nat := 118140960795 + 1807189 * 2 ^ 59
def prefixEnd_1807189 : Nat := 4983230072969 + 3 ^ 40 * 1807189 * 2
def baseEnd_1807189 : Nat := 927956590518235098426395

theorem tailTrace_1807189 : CollatzResearch.WordTrace tailWord_1807189 prefixEnd_1807189 927956590518235098426395 := by
  unfold tailWord_1807189
  simp only [CollatzResearch.WordTrace]
  refine ⟨65913597849870371153960621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43942398566580247435973747 65913597849870371153960621)
  ·
    refine ⟨24717599193701389182735233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65913597849870371153960621 24717599193701389182735233)
    ·
      refine ⟨18538199395276041887051425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24717599193701389182735233 18538199395276041887051425)
      ·
        refine ⟨13903649546457031415288569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18538199395276041887051425 13903649546457031415288569)
        ·
          refine ⟨10427737159842773561466427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13903649546457031415288569 10427737159842773561466427)
          ·
            refine ⟨15641605739764160342199641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10427737159842773561466427 15641605739764160342199641)
            ·
              refine ⟨11731204304823120256649731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15641605739764160342199641 11731204304823120256649731)
              ·
                refine ⟨17596806457234680384974597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11731204304823120256649731 17596806457234680384974597)
                ·
                  refine ⟨3299401210731502572182737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17596806457234680384974597 3299401210731502572182737)
                  ·
                    refine ⟨2474550908048626929137053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3299401210731502572182737 2474550908048626929137053)
                    ·
                      refine ⟨927956590518235098426395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2474550908048626929137053 927956590518235098426395)
                      ·
                        rfl

theorem cell23_1807189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1807189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807189 prefixEnd_1807189 := by exact prefixLift 1807189
  have htrace : WordTrace (prefixWord ++ tailWord_1807189) baseStart_1807189 baseEnd_1807189 := by
    simpa [prefixWord, tailWord_1807189, baseEnd_1807189] using wordTrace_append hprefix tailTrace_1807189
  have hstable : (prefixWord ++ tailWord_1807189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807189).length < 2 ^ (prefixWord ++ tailWord_1807189).sum := by decide
  have hdescent : baseEnd_1807189 < baseStart_1807189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807196 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1807196 : Nat := 118140960795 + 1807196 * 2 ^ 59
def prefixEnd_1807196 : Nat := 4983230072969 + 3 ^ 40 * 1807196 * 2
def baseEnd_1807196 : Nat := 309320061627605523679621

theorem tailTrace_1807196 : CollatzResearch.WordTrace tailWord_1807196 prefixEnd_1807196 309320061627605523679621 := by
  unfold tailWord_1807196
  simp only [CollatzResearch.WordTrace]
  refine ⟨32956926580422505674732721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43942568773896674232976961 32956926580422505674732721)
  ·
    refine ⟨24717694935316879256049541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32956926580422505674732721 24717694935316879256049541)
    ·
      refine ⟨4634567800371914860509289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24717694935316879256049541 4634567800371914860509289)
      ·
        refine ⟨3475925850278936145381967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4634567800371914860509289 3475925850278936145381967)
        ·
          refine ⟨5213888775418404218072951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475925850278936145381967 5213888775418404218072951)
          ·
            refine ⟨7820833163127606327109427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213888775418404218072951 7820833163127606327109427)
            ·
              refine ⟨11731249744691409490664141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7820833163127606327109427 11731249744691409490664141)
              ·
                refine ⟨4399218654259278558999053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11731249744691409490664141 4399218654259278558999053)
                ·
                  refine ⟨1649706995347229459624645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4399218654259278558999053 1649706995347229459624645)
                  ·
                    refine ⟨309320061627605523679621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1649706995347229459624645 309320061627605523679621)
                    ·
                      rfl

theorem cell23_1807196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1807196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807196 prefixEnd_1807196 := by exact prefixLift 1807196
  have htrace : WordTrace (prefixWord ++ tailWord_1807196) baseStart_1807196 baseEnd_1807196 := by
    simpa [prefixWord, tailWord_1807196, baseEnd_1807196] using wordTrace_append hprefix tailTrace_1807196
  have hstable : (prefixWord ++ tailWord_1807196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807196).length < 2 ^ (prefixWord ++ tailWord_1807196).sum := by decide
  have hdescent : baseEnd_1807196 < baseStart_1807196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807212 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_1807212 : Nat := 118140960795 + 1807212 * 2 ^ 59
def prefixEnd_1807212 : Nat := 4983230072969 + 3 ^ 40 * 1807212 * 2
def baseEnd_1807212 : Nat := 927968400573288508438789

theorem tailTrace_1807212 : CollatzResearch.WordTrace tailWord_1807212 prefixEnd_1807212 927968400573288508438789 := by
  unfold tailWord_1807212
  simp only [CollatzResearch.WordTrace]
  refine ⟨32957218364393523041023945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43942957819191364054698593 32957218364393523041023945)
  ·
    refine ⟨24717913773295142280767959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32957218364393523041023945 24717913773295142280767959)
    ·
      refine ⟨37076870659942713421151939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24717913773295142280767959 37076870659942713421151939)
      ·
        refine ⟨55615305989914070131727909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37076870659942713421151939 55615305989914070131727909)
        ·
          refine ⟨10427869873108888149698983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55615305989914070131727909 10427869873108888149698983)
          ·
            refine ⟨15641804809663332224548475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10427869873108888149698983 15641804809663332224548475)
            ·
              refine ⟨23462707214494998336822713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15641804809663332224548475 23462707214494998336822713)
              ·
                refine ⟨17597030410871248752617035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23462707214494998336822713 17597030410871248752617035)
                ·
                  refine ⟨26395545616306873128925553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17597030410871248752617035 26395545616306873128925553)
                  ·
                    refine ⟨19796659212230154846694165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26395545616306873128925553 19796659212230154846694165)
                    ·
                      refine ⟨927968400573288508438789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19796659212230154846694165 927968400573288508438789)
                      ·
                        rfl

theorem cell23_1807212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_1807212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807212 prefixEnd_1807212 := by exact prefixLift 1807212
  have htrace : WordTrace (prefixWord ++ tailWord_1807212) baseStart_1807212 baseEnd_1807212 := by
    simpa [prefixWord, tailWord_1807212, baseEnd_1807212] using wordTrace_append hprefix tailTrace_1807212
  have hstable : (prefixWord ++ tailWord_1807212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807212).length < 2 ^ (prefixWord ++ tailWord_1807212).sum := by decide
  have hdescent : baseEnd_1807212 < baseStart_1807212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807253 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_1807253 : Nat := 118140960795 + 1807253 * 2 ^ 59
def prefixEnd_1807253 : Nat := 4983230072969 + 3 ^ 40 * 1807253 * 2
def baseEnd_1807253 : Nat := 927989453280122848026101

theorem tailTrace_1807253 : CollatzResearch.WordTrace tailWord_1807253 prefixEnd_1807253 927989453280122848026101 := by
  unfold tailWord_1807253
  simp only [CollatzResearch.WordTrace]
  refine ⟨65915932121638510084290413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43943954747759006722860275 65915932121638510084290413)
  ·
    refine ⟨24718474545614441281608905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65915932121638510084290413 24718474545614441281608905)
    ·
      refine ⟨18538855909210830961206679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24718474545614441281608905 18538855909210830961206679)
      ·
        refine ⟨27808283863816246441810019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18538855909210830961206679 27808283863816246441810019)
        ·
          refine ⟨41712425795724369662715029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27808283863816246441810019 41712425795724369662715029)
          ·
            refine ⟨1955269959174579827939767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41712425795724369662715029 1955269959174579827939767)
            ·
              refine ⟨2932904938761869741909651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955269959174579827939767 2932904938761869741909651)
              ·
                refine ⟨4399357408142804612864477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932904938761869741909651 4399357408142804612864477)
                ·
                  refine ⟨1649759028053551729824179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4399357408142804612864477 1649759028053551729824179)
                  ·
                    refine ⟨2474638542080327594736269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1649759028053551729824179 2474638542080327594736269)
                    ·
                      refine ⟨927989453280122848026101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2474638542080327594736269 927989453280122848026101)
                      ·
                        rfl

theorem cell23_1807253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_1807253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807253 prefixEnd_1807253 := by exact prefixLift 1807253
  have htrace : WordTrace (prefixWord ++ tailWord_1807253) baseStart_1807253 baseEnd_1807253 := by
    simpa [prefixWord, tailWord_1807253, baseEnd_1807253] using wordTrace_append hprefix tailTrace_1807253
  have hstable : (prefixWord ++ tailWord_1807253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807253).length < 2 ^ (prefixWord ++ tailWord_1807253).sum := by decide
  have hdescent : baseEnd_1807253 < baseStart_1807253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807260 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 6]
def baseStart_1807260 : Nat := 118140960795 + 1807260 * 2 ^ 59
def prefixEnd_1807260 : Nat := 4983230072969 + 3 ^ 40 * 1807260 * 2
def baseEnd_1807260 : Nat := 103110338627189368959841

theorem tailTrace_1807260 : CollatzResearch.WordTrace tailWord_1807260 prefixEnd_1807260 103110338627189368959841 := by
  unfold tailWord_1807260
  simp only [CollatzResearch.WordTrace]
  refine ⟨32958093716306575139897617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43944124955075433519863489 32958093716306575139897617)
  ·
    refine ⟨24718570287229931354923213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32958093716306575139897617 24718570287229931354923213)
    ·
      refine ⟨9269463857711224258096205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24718570287229931354923213 9269463857711224258096205)
      ·
        refine ⟨3476048946641709096786077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9269463857711224258096205 3476048946641709096786077)
        ·
          refine ⟨1303518354990640911294779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3476048946641709096786077 1303518354990640911294779)
          ·
            refine ⟨1955277532485961366942169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303518354990640911294779 1955277532485961366942169)
            ·
              refine ⟨1466458149364471025206627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955277532485961366942169 1466458149364471025206627)
              ·
                refine ⟨2199687224046706537809941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466458149364471025206627 2199687224046706537809941)
                ·
                  refine ⟨103110338627189368959841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2199687224046706537809941 103110338627189368959841)
                  ·
                    rfl

theorem cell23_1807260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_1807260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807260 prefixEnd_1807260 := by exact prefixLift 1807260
  have htrace : WordTrace (prefixWord ++ tailWord_1807260) baseStart_1807260 baseEnd_1807260 := by
    simpa [prefixWord, tailWord_1807260, baseEnd_1807260] using wordTrace_append hprefix tailTrace_1807260
  have hstable : (prefixWord ++ tailWord_1807260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807260).length < 2 ^ (prefixWord ++ tailWord_1807260).sum := by decide
  have hdescent : baseEnd_1807260 < baseStart_1807260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807289 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1807289 : Nat := 118140960795 + 1807289 * 2 ^ 59
def prefixEnd_1807289 : Nat := 4983230072969 + 3 ^ 40 * 1807289 * 2
def baseEnd_1807289 : Nat := 928007938583684707175935

theorem tailTrace_1807289 : CollatzResearch.WordTrace tailWord_1807289 prefixEnd_1807289 928007938583684707175935 := by
  unfold tailWord_1807289
  simp only [CollatzResearch.WordTrace]
  refine ⟨65917245149508088232600921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43944830099672058821733947 65917245149508088232600921)
  ·
    refine ⟨49437933862131066174450691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65917245149508088232600921 49437933862131066174450691)
    ·
      refine ⟨74156900793196599261676037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49437933862131066174450691 74156900793196599261676037)
      ·
        refine ⟨13904418898724362361564257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74156900793196599261676037 13904418898724362361564257)
        ·
          refine ⟨10428314174043271771173193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13904418898724362361564257 10428314174043271771173193)
          ·
            refine ⟨7821235630532453828379895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10428314174043271771173193 7821235630532453828379895)
            ·
              refine ⟨11731853445798680742569843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7821235630532453828379895 11731853445798680742569843)
              ·
                refine ⟨17597780168698021113854765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11731853445798680742569843 17597780168698021113854765)
                ·
                  refine ⟨6599167563261757917695537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17597780168698021113854765 6599167563261757917695537)
                  ·
                    refine ⟨4949375672446318438271653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6599167563261757917695537 4949375672446318438271653)
                    ·
                      refine ⟨928007938583684707175935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4949375672446318438271653 928007938583684707175935)
                      ·
                        rfl

theorem cell23_1807289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1807289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807289 prefixEnd_1807289 := by exact prefixLift 1807289
  have htrace : WordTrace (prefixWord ++ tailWord_1807289) baseStart_1807289 baseEnd_1807289 := by
    simpa [prefixWord, tailWord_1807289, baseEnd_1807289] using wordTrace_append hprefix tailTrace_1807289
  have hstable : (prefixWord ++ tailWord_1807289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807289).length < 2 ^ (prefixWord ++ tailWord_1807289).sum := by decide
  have hdescent : baseEnd_1807289 < baseStart_1807289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807296 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 5]
def baseStart_1807296 : Nat := 118140960795 + 1807296 * 2 ^ 59
def prefixEnd_1807296 : Nat := 4983230072969 + 3 ^ 40 * 1807296 * 2
def baseEnd_1807296 : Nat := 928011532948266179788403

theorem tailTrace_1807296 : CollatzResearch.WordTrace tailWord_1807296 prefixEnd_1807296 928011532948266179788403 := by
  unfold tailWord_1807296
  simp only [CollatzResearch.WordTrace]
  refine ⟨32958750230241364214052871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43945000306988485618737161 32958750230241364214052871)
  ·
    refine ⟨49438125345362046321079307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32958750230241364214052871 49438125345362046321079307)
    ·
      refine ⟨74157188018043069481618961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49438125345362046321079307 74157188018043069481618961)
      ·
        refine ⟨55617891013532302111214221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74157188018043069481618961 55617891013532302111214221)
        ·
          refine ⟨20856709130074613291705333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55617891013532302111214221 20856709130074613291705333)
          ·
            refine ⟨1955316480944494996097375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20856709130074613291705333 1955316480944494996097375)
            ·
              refine ⟨2932974721416742494146063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955316480944494996097375 2932974721416742494146063)
              ·
                refine ⟨4399462082125113741219095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932974721416742494146063 4399462082125113741219095)
                ·
                  refine ⟨6599193123187670611828643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399462082125113741219095 6599193123187670611828643)
                  ·
                    refine ⟨9898789684781505917742965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6599193123187670611828643 9898789684781505917742965)
                    ·
                      refine ⟨928011532948266179788403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9898789684781505917742965 928011532948266179788403)
                      ·
                        rfl

theorem cell23_1807296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_1807296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807296 prefixEnd_1807296 := by exact prefixLift 1807296
  have htrace : WordTrace (prefixWord ++ tailWord_1807296) baseStart_1807296 baseEnd_1807296 := by
    simpa [prefixWord, tailWord_1807296, baseEnd_1807296] using wordTrace_append hprefix tailTrace_1807296
  have hstable : (prefixWord ++ tailWord_1807296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807296).length < 2 ^ (prefixWord ++ tailWord_1807296).sum := by decide
  have hdescent : baseEnd_1807296 < baseStart_1807296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807304 : List Nat := [2, 1, 3, 1, 6, 1, 2, 2, 1, 1, 3]
def baseStart_1807304 : Nat := 118140960795 + 1807304 * 2 ^ 59
def prefixEnd_1807304 : Nat := 4983230072969 + 3 ^ 40 * 1807304 * 2
def baseEnd_1807304 : Nat := 928015640793502148488367

theorem tailTrace_1807304 : CollatzResearch.WordTrace tailWord_1807304 prefixEnd_1807304 928015640793502148488367 := by
  unfold tailWord_1807304
  simp only [CollatzResearch.WordTrace]
  refine ⟨32958896122226872897198483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43945194829635830529597977 32958896122226872897198483)
  ·
    refine ⟨49438344183340309345797725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32958896122226872897198483 49438344183340309345797725)
    ·
      refine ⟨18539379068752616004674147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49438344183340309345797725 18539379068752616004674147)
      ·
        refine ⟨27809068603128924007011221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18539379068752616004674147 27809068603128924007011221)
        ·
          refine ⟨1303550090771668312828651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27809068603128924007011221 1303550090771668312828651)
          ·
            refine ⟨1955325136157502469242977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303550090771668312828651 1955325136157502469242977)
            ·
              refine ⟨1466493852118126851932233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955325136157502469242977 1466493852118126851932233)
              ·
                refine ⟨1099870389088595138949175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466493852118126851932233 1099870389088595138949175)
                ·
                  refine ⟨1649805583632892708423763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099870389088595138949175 1649805583632892708423763)
                  ·
                    refine ⟨2474708375449339062635645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1649805583632892708423763 2474708375449339062635645)
                    ·
                      refine ⟨928015640793502148488367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2474708375449339062635645 928015640793502148488367)
                      ·
                        rfl

theorem cell23_1807304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_1807304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807304 prefixEnd_1807304 := by exact prefixLift 1807304
  have htrace : WordTrace (prefixWord ++ tailWord_1807304) baseStart_1807304 baseEnd_1807304 := by
    simpa [prefixWord, tailWord_1807304, baseEnd_1807304] using wordTrace_append hprefix tailTrace_1807304
  have hstable : (prefixWord ++ tailWord_1807304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807304).length < 2 ^ (prefixWord ++ tailWord_1807304).sum := by decide
  have hdescent : baseEnd_1807304 < baseStart_1807304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807316 : List Nat := [2, 4, 1, 2, 1, 4, 1, 8]
def baseStart_1807316 : Nat := 118140960795 + 1807316 * 2 ^ 59
def prefixEnd_1807316 : Nat := 4983230072969 + 3 ^ 40 * 1807316 * 2
def baseEnd_1807316 : Nat := 34371177872642818575493

theorem tailTrace_1807316 : CollatzResearch.WordTrace tailWord_1807316 prefixEnd_1807316 34371177872642818575493 := by
  unfold tailWord_1807316
  simp only [CollatzResearch.WordTrace]
  refine ⟨32959114960205135921916901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43945486613606847895889201 32959114960205135921916901)
  ·
    refine ⟨6179834055038462985359419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32959114960205135921916901 6179834055038462985359419)
    ·
      refine ⟨9269751082557694478039129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6179834055038462985359419 9269751082557694478039129)
      ·
        refine ⟨6952313311918270858529347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9269751082557694478039129 6952313311918270858529347)
        ·
          refine ⟨10428469967877406287794021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6952313311918270858529347 10428469967877406287794021)
          ·
            refine ⟨1955338118977013678961379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10428469967877406287794021 1955338118977013678961379)
            ·
              refine ⟨2933007178465520518442069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955338118977013678961379 2933007178465520518442069)
              ·
                refine ⟨34371177872642818575493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2933007178465520518442069 34371177872642818575493)
                ·
                  rfl

theorem cell23_1807316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 8].length) (baseStart_1807316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807316 prefixEnd_1807316 := by exact prefixLift 1807316
  have htrace : WordTrace (prefixWord ++ tailWord_1807316) baseStart_1807316 baseEnd_1807316 := by
    simpa [prefixWord, tailWord_1807316, baseEnd_1807316] using wordTrace_append hprefix tailTrace_1807316
  have hstable : (prefixWord ++ tailWord_1807316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807316).length < 2 ^ (prefixWord ++ tailWord_1807316).sum := by decide
  have hdescent : baseEnd_1807316 < baseStart_1807316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807333 : List Nat := [1, 3, 1, 6, 1, 1, 3, 7]
def baseStart_1807333 : Nat := 118140960795 + 1807333 * 2 ^ 59
def prefixEnd_1807333 : Nat := 4983230072969 + 3 ^ 40 * 1807333 * 2
def baseEnd_1807333 : Nat := 34371501175277130926879

theorem tailTrace_1807333 : CollatzResearch.WordTrace tailWord_1807333 prefixEnd_1807333 34371501175277130926879 := by
  unfold tailWord_1807333
  simp only [CollatzResearch.WordTrace]
  refine ⟨65918849961348683747202653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43945899974232455831468435 65918849961348683747202653)
  ·
    refine ⟨24719568735505756405200995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65918849961348683747202653 24719568735505756405200995)
    ·
      refine ⟨37079353103258634607801493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24719568735505756405200995 37079353103258634607801493)
      ·
        refine ⟨1738094676715248497240695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37079353103258634607801493 1738094676715248497240695)
        ·
          refine ⟨2607142015072872745861043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738094676715248497240695 2607142015072872745861043)
          ·
            refine ⟨3910713022609309118791565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607142015072872745861043 3910713022609309118791565)
            ·
              refine ⟨1466517383478490919546837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3910713022609309118791565 1466517383478490919546837)
              ·
                refine ⟨34371501175277130926879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1466517383478490919546837 34371501175277130926879)
                ·
                  rfl

theorem cell23_1807333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 7].length) (baseStart_1807333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807333 prefixEnd_1807333 := by exact prefixLift 1807333
  have htrace : WordTrace (prefixWord ++ tailWord_1807333) baseStart_1807333 baseEnd_1807333 := by
    simpa [prefixWord, tailWord_1807333, baseEnd_1807333] using wordTrace_append hprefix tailTrace_1807333
  have hstable : (prefixWord ++ tailWord_1807333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807333).length < 2 ^ (prefixWord ++ tailWord_1807333).sum := by decide
  have hdescent : baseEnd_1807333 < baseStart_1807333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807353 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 1, 3, 2]
def baseStart_1807353 : Nat := 118140960795 + 1807353 * 2 ^ 59
def prefixEnd_1807353 : Nat := 4983230072969 + 3 ^ 40 * 1807353 * 2
def baseEnd_1807353 : Nat := 928040801345572456775641

theorem tailTrace_1807353 : CollatzResearch.WordTrace tailWord_1807353 prefixEnd_1807353 928040801345572456775641 := by
  unfold tailWord_1807353
  simp only [CollatzResearch.WordTrace]
  refine ⟨65919579421276227162930713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43946386280850818108620475 65919579421276227162930713)
  ·
    refine ⟨49439684565957170372198035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65919579421276227162930713 49439684565957170372198035)
    ·
      refine ⟨74159526848935755558297053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49439684565957170372198035 74159526848935755558297053)
      ·
        refine ⟨27809822568350908334361395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74159526848935755558297053 27809822568350908334361395)
        ·
          refine ⟨41714733852526362501542093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27809822568350908334361395 41714733852526362501542093)
          ·
            refine ⟨15643025194697385938078285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41714733852526362501542093 15643025194697385938078285)
            ·
              refine ⟨5866134448011519726779357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15643025194697385938078285 5866134448011519726779357)
              ·
                refine ⟨2199800418004319897542259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5866134448011519726779357 2199800418004319897542259)
                ·
                  refine ⟨3299700627006479846313389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199800418004319897542259 3299700627006479846313389)
                  ·
                    refine ⟨1237387735127429942367521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3299700627006479846313389 1237387735127429942367521)
                    ·
                      refine ⟨928040801345572456775641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1237387735127429942367521 928040801345572456775641)
                      ·
                        rfl

theorem cell23_1807353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_1807353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807353 prefixEnd_1807353 := by exact prefixLift 1807353
  have htrace : WordTrace (prefixWord ++ tailWord_1807353) baseStart_1807353 baseEnd_1807353 := by
    simpa [prefixWord, tailWord_1807353, baseEnd_1807353] using wordTrace_append hprefix tailTrace_1807353
  have hstable : (prefixWord ++ tailWord_1807353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807353).length < 2 ^ (prefixWord ++ tailWord_1807353).sum := by decide
  have hdescent : baseEnd_1807353 < baseStart_1807353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807369 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 3]
def baseStart_1807369 : Nat := 118140960795 + 1807369 * 2 ^ 59
def prefixEnd_1807369 : Nat := 4983230072969 + 3 ^ 40 * 1807369 * 2
def baseEnd_1807369 : Nat := 928049017036044394175567

theorem tailTrace_1807369 : CollatzResearch.WordTrace tailWord_1807369 prefixEnd_1807369 928049017036044394175567 := by
  unfold tailWord_1807369
  simp only [CollatzResearch.WordTrace]
  refine ⟨65920162989218261895513161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43946775326145507930342107 65920162989218261895513161)
  ·
    refine ⟨49440122241913696421634871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65920162989218261895513161 49440122241913696421634871)
    ·
      refine ⟨74160183362870544632452307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49440122241913696421634871 74160183362870544632452307)
      ·
        refine ⟨111240275044305816948678461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74160183362870544632452307 111240275044305816948678461)
        ·
          refine ⟨41715103141614681355754423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111240275044305816948678461 41715103141614681355754423)
          ·
            refine ⟨62572654712422022033631635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41715103141614681355754423 62572654712422022033631635)
            ·
              refine ⟨93858982068633033050447453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62572654712422022033631635 93858982068633033050447453)
              ·
                refine ⟨35197118275737387393917795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93858982068633033050447453 35197118275737387393917795)
                ·
                  refine ⟨52795677413606081090876693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35197118275737387393917795 52795677413606081090876693)
                  ·
                    refine ⟨2474797378762785051134845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52795677413606081090876693 2474797378762785051134845)
                    ·
                      refine ⟨928049017036044394175567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2474797378762785051134845 928049017036044394175567)
                      ·
                        rfl

theorem cell23_1807369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_1807369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807369 prefixEnd_1807369 := by exact prefixLift 1807369
  have htrace : WordTrace (prefixWord ++ tailWord_1807369) baseStart_1807369 baseEnd_1807369 := by
    simpa [prefixWord, tailWord_1807369, baseEnd_1807369] using wordTrace_append hprefix tailTrace_1807369
  have hstable : (prefixWord ++ tailWord_1807369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807369).length < 2 ^ (prefixWord ++ tailWord_1807369).sum := by decide
  have hdescent : baseEnd_1807369 < baseStart_1807369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807429 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_1807429 : Nat := 118140960795 + 1807429 * 2 ^ 59
def prefixEnd_1807429 : Nat := 4983230072969 + 3 ^ 40 * 1807429 * 2
def baseEnd_1807429 : Nat := 928079825875314159425291

theorem tailTrace_1807429 : CollatzResearch.WordTrace tailWord_1807429 prefixEnd_1807429 928079825875314159425291 := by
  unfold tailWord_1807429
  simp only [CollatzResearch.WordTrace]
  refine ⟨65922351369000892142697341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43948234246000594761798227 65922351369000892142697341)
  ·
    refine ⟨24720881763375334553511503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65922351369000892142697341 24720881763375334553511503)
    ·
      refine ⟨37081322645063001830267255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24720881763375334553511503 37081322645063001830267255)
      ·
        refine ⟨55621983967594502745400883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37081322645063001830267255 55621983967594502745400883)
        ·
          refine ⟨83432975951391754118101325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55621983967594502745400883 83432975951391754118101325)
          ·
            refine ⟨31287365981771907794287997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83432975951391754118101325 31287365981771907794287997)
            ·
              refine ⟨11732762243164465422857999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31287365981771907794287997 11732762243164465422857999)
              ·
                refine ⟨17599143364746698134286999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11732762243164465422857999 17599143364746698134286999)
                ·
                  refine ⟨26398715047120047201430499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17599143364746698134286999 26398715047120047201430499)
                  ·
                    refine ⟨39598072570680070802145749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26398715047120047201430499 39598072570680070802145749)
                    ·
                      refine ⟨928079825875314159425291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39598072570680070802145749 928079825875314159425291)
                      ·
                        rfl

theorem cell23_1807429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_1807429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807429 prefixEnd_1807429 := by exact prefixLift 1807429
  have htrace : WordTrace (prefixWord ++ tailWord_1807429) baseStart_1807429 baseEnd_1807429 := by
    simpa [prefixWord, tailWord_1807429, baseEnd_1807429] using wordTrace_append hprefix tailTrace_1807429
  have hstable : (prefixWord ++ tailWord_1807429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807429).length < 2 ^ (prefixWord ++ tailWord_1807429).sum := by decide
  have hdescent : baseEnd_1807429 < baseStart_1807429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807530 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 6]
def baseStart_1807530 : Nat := 118140960795 + 1807530 * 2 ^ 59
def prefixEnd_1807530 : Nat := 4983230072969 + 3 ^ 40 * 1807530 * 2
def baseEnd_1807530 : Nat := 103125743046824251584703

theorem tailTrace_1807530 : CollatzResearch.WordTrace tailWord_1807530 prefixEnd_1807530 103125743046824251584703 := by
  unfold tailWord_1807530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481508785408746598031011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43950690094423324261416029 16481508785408746598031011)
  ·
    refine ⟨24722263178113119897046517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16481508785408746598031011 24722263178113119897046517)
    ·
      refine ⟨2317712172948104990348111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24722263178113119897046517 2317712172948104990348111)
      ·
        refine ⟨3476568259422157485522167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2317712172948104990348111 3476568259422157485522167)
        ·
          refine ⟨5214852389133236228283251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476568259422157485522167 5214852389133236228283251)
          ·
            refine ⟨7822278583699854342424877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214852389133236228283251 7822278583699854342424877)
            ·
              refine ⟨2933354468887445378409329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7822278583699854342424877 2933354468887445378409329)
              ·
                refine ⟨2200015851665584033806997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933354468887445378409329 2200015851665584033806997)
                ·
                  refine ⟨103125743046824251584703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2200015851665584033806997 103125743046824251584703)
                  ·
                    rfl

theorem cell23_1807530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_1807530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807530 prefixEnd_1807530 := by exact prefixLift 1807530
  have htrace : WordTrace (prefixWord ++ tailWord_1807530) baseStart_1807530 baseEnd_1807530 := by
    simpa [prefixWord, tailWord_1807530, baseEnd_1807530] using wordTrace_append hprefix tailTrace_1807530
  have hstable : (prefixWord ++ tailWord_1807530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807530).length < 2 ^ (prefixWord ++ tailWord_1807530).sum := by decide
  have hdescent : baseEnd_1807530 < baseStart_1807530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807550 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_1807550 : Nat := 118140960795 + 1807550 * 2 ^ 59
def prefixEnd_1807550 : Nat := 4983230072969 + 3 ^ 40 * 1807550 * 2
def baseEnd_1807550 : Nat := 928141957034508186012235

theorem tailTrace_1807550 : CollatzResearch.WordTrace tailWord_1807550 prefixEnd_1807550 928141957034508186012235 := by
  unfold tailWord_1807550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240845575195316225981513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43951176401041686538568069 8240845575195316225981513)
  ·
    refine ⟨6180634181396487169486135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8240845575195316225981513 6180634181396487169486135)
    ·
      refine ⟨9270951272094730754229203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6180634181396487169486135 9270951272094730754229203)
      ·
        refine ⟨13906426908142096131343805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270951272094730754229203 13906426908142096131343805)
        ·
          refine ⟨5214910090553286049253927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13906426908142096131343805 5214910090553286049253927)
          ·
            refine ⟨7822365135829929073880891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214910090553286049253927 7822365135829929073880891)
            ·
              refine ⟨11733547703744893610821337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7822365135829929073880891 11733547703744893610821337)
              ·
                refine ⟨8800160777808670208116003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11733547703744893610821337 8800160777808670208116003)
                ·
                  refine ⟨13200241166713005312174005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800160777808670208116003 13200241166713005312174005)
                  ·
                    refine ⟨1237522609379344248016313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13200241166713005312174005 1237522609379344248016313)
                    ·
                      refine ⟨928141957034508186012235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1237522609379344248016313 928141957034508186012235)
                      ·
                        rfl

theorem cell23_1807550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_1807550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807550 prefixEnd_1807550 := by exact prefixLift 1807550
  have htrace : WordTrace (prefixWord ++ tailWord_1807550) baseStart_1807550 baseEnd_1807550 := by
    simpa [prefixWord, tailWord_1807550, baseEnd_1807550] using wordTrace_append hprefix tailTrace_1807550
  have hstable : (prefixWord ++ tailWord_1807550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807550).length < 2 ^ (prefixWord ++ tailWord_1807550).sum := by decide
  have hdescent : baseEnd_1807550 < baseStart_1807550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807591 : List Nat := [1, 1, 5, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1807591 : Nat := 118140960795 + 1807591 * 2 ^ 59
def prefixEnd_1807591 : Nat := 4983230072969 + 3 ^ 40 * 1807591 * 2
def baseEnd_1807591 : Nat := 928163009741342525599547

theorem tailTrace_1807591 : CollatzResearch.WordTrace tailWord_1807591 prefixEnd_1807591 928163009741342525599547 := by
  unfold tailWord_1807591
  simp only [CollatzResearch.WordTrace]
  refine ⟨65928259994413993810094627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43952173329609329206729751 65928259994413993810094627)
  ·
    refine ⟨98892389991620990715141941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65928259994413993810094627 98892389991620990715141941)
    ·
      refine ⟨9271161561714467879544557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98892389991620990715141941 9271161561714467879544557)
      ·
        refine ⟨3476685585642925454829209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9271161561714467879544557 3476685585642925454829209)
        ·
          refine ⟨2607514189232194091121907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3476685585642925454829209 2607514189232194091121907)
          ·
            refine ⟨3911271283848291136682861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607514189232194091121907 3911271283848291136682861)
            ·
              refine ⟨1466726731443109176256073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3911271283848291136682861 1466726731443109176256073)
              ·
                refine ⟨1100045048582331882192055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466726731443109176256073 1100045048582331882192055)
                ·
                  refine ⟨1650067572873497823288083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100045048582331882192055 1650067572873497823288083)
                  ·
                    refine ⟨2475101359310246734932125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1650067572873497823288083 2475101359310246734932125)
                    ·
                      refine ⟨928163009741342525599547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2475101359310246734932125 928163009741342525599547)
                      ·
                        rfl

theorem cell23_1807591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1807591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807591 prefixEnd_1807591 := by exact prefixLift 1807591
  have htrace : WordTrace (prefixWord ++ tailWord_1807591) baseStart_1807591 baseEnd_1807591 := by
    simpa [prefixWord, tailWord_1807591, baseEnd_1807591] using wordTrace_append hprefix tailTrace_1807591
  have hstable : (prefixWord ++ tailWord_1807591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807591).length < 2 ^ (prefixWord ++ tailWord_1807591).sum := by decide
  have hdescent : baseEnd_1807591 < baseStart_1807591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807617 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_1807617 : Nat := 118140960795 + 1807617 * 2 ^ 59
def prefixEnd_1807617 : Nat := 4983230072969 + 3 ^ 40 * 1807617 * 2
def baseEnd_1807617 : Nat := 928176360238359423874427

theorem tailTrace_1807617 : CollatzResearch.WordTrace tailWord_1807617 prefixEnd_1807617 928176360238359423874427 := by
  unfold tailWord_1807617
  simp only [CollatzResearch.WordTrace]
  refine ⟨65929208292319800250541105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43952805528213200167027403 65929208292319800250541105)
  ·
    refine ⟨49446906219239850187905829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65929208292319800250541105 49446906219239850187905829)
    ·
      refine ⟨9271294916107471910232343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49446906219239850187905829 9271294916107471910232343)
      ·
        refine ⟨13906942374161207865348515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9271294916107471910232343 13906942374161207865348515)
        ·
          refine ⟨20860413561241811798022773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13906942374161207865348515 20860413561241811798022773)
          ·
            refine ⟨1955663771366419856064635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20860413561241811798022773 1955663771366419856064635)
            ·
              refine ⟨2933495657049629784096953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955663771366419856064635 2933495657049629784096953)
              ·
                refine ⟨2200121742787222338072715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933495657049629784096953 2200121742787222338072715)
                ·
                  refine ⟨3300182614180833507109073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200121742787222338072715 3300182614180833507109073)
                  ·
                    refine ⟨2475136960635625130331805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3300182614180833507109073 2475136960635625130331805)
                    ·
                      refine ⟨928176360238359423874427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2475136960635625130331805 928176360238359423874427)
                      ·
                        rfl

theorem cell23_1807617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_1807617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807617 prefixEnd_1807617 := by exact prefixLift 1807617
  have htrace : WordTrace (prefixWord ++ tailWord_1807617) baseStart_1807617 baseEnd_1807617 := by
    simpa [prefixWord, tailWord_1807617, baseEnd_1807617] using wordTrace_append hprefix tailTrace_1807617
  have hstable : (prefixWord ++ tailWord_1807617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807617).length < 2 ^ (prefixWord ++ tailWord_1807617).sum := by decide
  have hdescent : baseEnd_1807617 < baseStart_1807617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807630 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1807630 : Nat := 118140960795 + 1807630 * 2 ^ 59
def prefixEnd_1807630 : Nat := 4983230072969 + 3 ^ 40 * 1807630 * 2
def baseEnd_1807630 : Nat := 928183035486867873011867

theorem tailTrace_1807630 : CollatzResearch.WordTrace tailWord_1807630 prefixEnd_1807630 928183035486867873011867 := by
  unfold tailWord_1807630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241210305159087933845543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43953121627515135647176229 8241210305159087933845543)
  ·
    refine ⟨12361815457738631900768315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241210305159087933845543 12361815457738631900768315)
    ·
      refine ⟨18542723186607947851152473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12361815457738631900768315 18542723186607947851152473)
      ·
        refine ⟨13907042389955960888364355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18542723186607947851152473 13907042389955960888364355)
        ·
          refine ⟨20860563584933941332546533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13907042389955960888364355 20860563584933941332546533)
          ·
            refine ⟨3911355672175113999852475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20860563584933941332546533 3911355672175113999852475)
            ·
              refine ⟨5867033508262670999778713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3911355672175113999852475 5867033508262670999778713)
              ·
                refine ⟨4400275131197003249834035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5867033508262670999778713 4400275131197003249834035)
                ·
                  refine ⟨6600412696795504874751053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400275131197003249834035 6600412696795504874751053)
                  ·
                    refine ⟨2475154761298314328031645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6600412696795504874751053 2475154761298314328031645)
                    ·
                      refine ⟨928183035486867873011867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2475154761298314328031645 928183035486867873011867)
                      ·
                        rfl

theorem cell23_1807630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1807630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807630 prefixEnd_1807630 := by exact prefixLift 1807630
  have htrace : WordTrace (prefixWord ++ tailWord_1807630) baseStart_1807630 baseEnd_1807630 := by
    simpa [prefixWord, tailWord_1807630, baseEnd_1807630] using wordTrace_append hprefix tailTrace_1807630
  have hstable : (prefixWord ++ tailWord_1807630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807630).length < 2 ^ (prefixWord ++ tailWord_1807630).sum := by decide
  have hdescent : baseEnd_1807630 < baseStart_1807630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807634 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1807634 : Nat := 118140960795 + 1807634 * 2 ^ 59
def prefixEnd_1807634 : Nat := 4983230072969 + 3 ^ 40 * 1807634 * 2
def baseEnd_1807634 : Nat := 928185089409485857361849

theorem tailTrace_1807634 : CollatzResearch.WordTrace tailWord_1807634 prefixEnd_1807634 928185089409485857361849 := by
  unfold tailWord_1807634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16482457083314553038477489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43953218888838808102606637 16482457083314553038477489)
  ·
    refine ⟨12361842812485914778858117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16482457083314553038477489 12361842812485914778858117)
    ·
      refine ⟨2317845527341109021035897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12361842812485914778858117 2317845527341109021035897)
      ·
        refine ⟨1738384145505831765776923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2317845527341109021035897 1738384145505831765776923)
        ·
          refine ⟨2607576218258747648665385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738384145505831765776923 2607576218258747648665385)
          ·
            refine ⟨1955682163694060736499039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2607576218258747648665385 1955682163694060736499039)
            ·
              refine ⟨2933523245541091104748559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955682163694060736499039 2933523245541091104748559)
              ·
                refine ⟨4400284868311636657122839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933523245541091104748559 4400284868311636657122839)
                ·
                  refine ⟨6600427302467454985684259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400284868311636657122839 6600427302467454985684259)
                  ·
                    refine ⟨9900640953701182478526389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6600427302467454985684259 9900640953701182478526389)
                    ·
                      refine ⟨928185089409485857361849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9900640953701182478526389 928185089409485857361849)
                      ·
                        rfl

theorem cell23_1807634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1807634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807634 prefixEnd_1807634 := by exact prefixLift 1807634
  have htrace : WordTrace (prefixWord ++ tailWord_1807634) baseStart_1807634 baseEnd_1807634 := by
    simpa [prefixWord, tailWord_1807634, baseEnd_1807634] using wordTrace_append hprefix tailTrace_1807634
  have hstable : (prefixWord ++ tailWord_1807634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807634).length < 2 ^ (prefixWord ++ tailWord_1807634).sum := by decide
  have hdescent : baseEnd_1807634 < baseStart_1807634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807648 : List Nat := [2, 1, 1, 5, 3, 2, 2, 2, 1, 2, 2]
def baseStart_1807648 : Nat := 118140960795 + 1807648 * 2 ^ 59
def prefixEnd_1807648 : Nat := 4983230072969 + 3 ^ 40 * 1807648 * 2
def baseEnd_1807648 : Nat := 928192278138648802586785

theorem tailTrace_1807648 : CollatzResearch.WordTrace tailWord_1807648 prefixEnd_1807648 928192278138648802586785 := by
  unfold tailWord_1807648
  simp only [CollatzResearch.WordTrace]
  refine ⟨32965169477603746272459799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43953559303471661696613065 32965169477603746272459799)
  ·
    refine ⟨49447754216405619408689699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32965169477603746272459799 49447754216405619408689699)
    ·
      refine ⟨74171631324608429113034549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49447754216405619408689699 74171631324608429113034549)
      ·
        refine ⟨6953590436682040229346989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74171631324608429113034549 6953590436682040229346989)
        ·
          refine ⟨2607596413755765086005121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6953590436682040229346989 2607596413755765086005121)
          ·
            refine ⟨1955697310316823814503841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2607596413755765086005121 1955697310316823814503841)
            ·
              refine ⟨1466772982737617860877881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955697310316823814503841 1466772982737617860877881)
              ·
                refine ⟨1100079737053213395658411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466772982737617860877881 1100079737053213395658411)
                ·
                  refine ⟨1650119605579820093487617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100079737053213395658411 1650119605579820093487617)
                  ·
                    refine ⟨1237589704184865070115713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1650119605579820093487617 1237589704184865070115713)
                    ·
                      refine ⟨928192278138648802586785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1237589704184865070115713 928192278138648802586785)
                      ·
                        rfl

theorem cell23_1807648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_1807648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807648 prefixEnd_1807648 := by exact prefixLift 1807648
  have htrace : WordTrace (prefixWord ++ tailWord_1807648) baseStart_1807648 baseEnd_1807648 := by
    simpa [prefixWord, tailWord_1807648, baseEnd_1807648] using wordTrace_append hprefix tailTrace_1807648
  have hstable : (prefixWord ++ tailWord_1807648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807648).length < 2 ^ (prefixWord ++ tailWord_1807648).sum := by decide
  have hdescent : baseEnd_1807648 < baseStart_1807648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807653 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_1807653 : Nat := 118140960795 + 1807653 * 2 ^ 59
def prefixEnd_1807653 : Nat := 4983230072969 + 3 ^ 40 * 1807653 * 2
def baseEnd_1807653 : Nat := 928194845541921283024261

theorem tailTrace_1807653 : CollatzResearch.WordTrace tailWord_1807653 prefixEnd_1807653 928194845541921283024261 := by
  unfold tailWord_1807653
  simp only [CollatzResearch.WordTrace]
  refine ⟨65930521320189378398851613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43953680880126252265901075 65930521320189378398851613)
  ·
    refine ⟨24723945495071016899569355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65930521320189378398851613 24723945495071016899569355)
    ·
      refine ⟨37085918242606525349354033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24723945495071016899569355 37085918242606525349354033)
      ·
        refine ⟨27814438681954894012015525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37085918242606525349354033 27814438681954894012015525)
        ·
          refine ⟨5215207252866542627252911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27814438681954894012015525 5215207252866542627252911)
          ·
            refine ⟨7822810879299813940879367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215207252866542627252911 7822810879299813940879367)
            ·
              refine ⟨11734216318949720911319051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7822810879299813940879367 11734216318949720911319051)
              ·
                refine ⟨17601324478424581366978577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11734216318949720911319051 17601324478424581366978577)
                ·
                  refine ⟨13200993358818436025233933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17601324478424581366978577 13200993358818436025233933)
                  ·
                    refine ⟨4950372509556913509462725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13200993358818436025233933 4950372509556913509462725)
                    ·
                      refine ⟨928194845541921283024261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4950372509556913509462725 928194845541921283024261)
                      ·
                        rfl

theorem cell23_1807653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_1807653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807653 prefixEnd_1807653 := by exact prefixLift 1807653
  have htrace : WordTrace (prefixWord ++ tailWord_1807653) baseStart_1807653 baseEnd_1807653 := by
    simpa [prefixWord, tailWord_1807653, baseEnd_1807653] using wordTrace_append hprefix tailTrace_1807653
  have hstable : (prefixWord ++ tailWord_1807653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807653).length < 2 ^ (prefixWord ++ tailWord_1807653).sum := by decide
  have hdescent : baseEnd_1807653 < baseStart_1807653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807763 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 3]
def baseStart_1807763 : Nat := 118140960795 + 1807763 * 2 ^ 59
def prefixEnd_1807763 : Nat := 4983230072969 + 3 ^ 40 * 1807763 * 2
def baseEnd_1807763 : Nat := 928251328413915852648755

theorem tailTrace_1807763 : CollatzResearch.WordTrace tailWord_1807763 prefixEnd_1807763 928251328413915852648755 := by
  unfold tailWord_1807763
  simp only [CollatzResearch.WordTrace]
  refine ⟨65934533349790867185355943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43956355566527244790237295 65934533349790867185355943)
  ·
    refine ⟨98901800024686300778033915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65934533349790867185355943 98901800024686300778033915)
    ·
      refine ⟨148352700037029451167050873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98901800024686300778033915 148352700037029451167050873)
      ·
        refine ⟨111264525027772088375288155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148352700037029451167050873 111264525027772088375288155)
        ·
          refine ⟨166896787541658132562932233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111264525027772088375288155 166896787541658132562932233)
          ·
            refine ⟨125172590656243599422199175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166896787541658132562932233 125172590656243599422199175)
            ·
              refine ⟨187758885984365399133298763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125172590656243599422199175 187758885984365399133298763)
              ·
                refine ⟨281638328976548098699948145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187758885984365399133298763 281638328976548098699948145)
                ·
                  refine ⟨211228746732411074024961109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281638328976548098699948145 211228746732411074024961109)
                  ·
                    refine ⟨2475336875770442273730013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 211228746732411074024961109 2475336875770442273730013)
                    ·
                      refine ⟨928251328413915852648755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2475336875770442273730013 928251328413915852648755)
                      ·
                        rfl

theorem cell23_1807763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_1807763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807763 prefixEnd_1807763 := by exact prefixLift 1807763
  have htrace : WordTrace (prefixWord ++ tailWord_1807763) baseStart_1807763 baseEnd_1807763 := by
    simpa [prefixWord, tailWord_1807763, baseEnd_1807763] using wordTrace_append hprefix tailTrace_1807763
  have hstable : (prefixWord ++ tailWord_1807763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807763).length < 2 ^ (prefixWord ++ tailWord_1807763).sum := by decide
  have hdescent : baseEnd_1807763 < baseStart_1807763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807780 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_1807780 : Nat := 118140960795 + 1807780 * 2 ^ 59
def prefixEnd_1807780 : Nat := 4983230072969 + 3 ^ 40 * 1807780 * 2
def baseEnd_1807780 : Nat := 928260057585042286136177

theorem tailTrace_1807780 : CollatzResearch.WordTrace tailWord_1807780 prefixEnd_1807780 928260057585042286136177 := by
  unfold tailWord_1807780
  simp only [CollatzResearch.WordTrace]
  refine ⟨32967576695364639544362397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43956768927152852725816529 32967576695364639544362397)
  ·
    refine ⟨12362841260761739829135899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32967576695364639544362397 12362841260761739829135899)
    ·
      refine ⟨18544261891142609743703849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12362841260761739829135899 18544261891142609743703849)
      ·
        refine ⟨13908196418356957307777887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18544261891142609743703849 13908196418356957307777887)
        ·
          refine ⟨20862294627535435961666831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13908196418356957307777887 20862294627535435961666831)
          ·
            refine ⟨31293441941303153942500247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20862294627535435961666831 31293441941303153942500247)
            ·
              refine ⟨46940162911954730913750371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31293441941303153942500247 46940162911954730913750371)
              ·
                refine ⟨70410244367932096370625557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46940162911954730913750371 70410244367932096370625557)
                ·
                  refine ⟨3300480204746817017373073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70410244367932096370625557 3300480204746817017373073)
                  ·
                    refine ⟨2475360153560112763029805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3300480204746817017373073 2475360153560112763029805)
                    ·
                      refine ⟨928260057585042286136177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2475360153560112763029805 928260057585042286136177)
                      ·
                        rfl

theorem cell23_1807780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_1807780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807780 prefixEnd_1807780 := by exact prefixLift 1807780
  have htrace : WordTrace (prefixWord ++ tailWord_1807780) baseStart_1807780 baseEnd_1807780 := by
    simpa [prefixWord, tailWord_1807780, baseEnd_1807780] using wordTrace_append hprefix tailTrace_1807780
  have hstable : (prefixWord ++ tailWord_1807780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807780).length < 2 ^ (prefixWord ++ tailWord_1807780).sum := by decide
  have hdescent : baseEnd_1807780 < baseStart_1807780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807797 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1807797 : Nat := 118140960795 + 1807797 * 2 ^ 59
def prefixEnd_1807797 : Nat := 4983230072969 + 3 ^ 40 * 1807797 * 2
def baseEnd_1807797 : Nat := 928268786756168719623599

theorem tailTrace_1807797 : CollatzResearch.WordTrace tailWord_1807797 prefixEnd_1807797 928268786756168719623599 := by
  unfold tailWord_1807797
  simp only [CollatzResearch.WordTrace]
  refine ⟨65935773431667690992093645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43957182287778460661395763 65935773431667690992093645)
  ·
    refine ⟨24725915036875384122035117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65935773431667690992093645 24725915036875384122035117)
    ·
      refine ⟨9272218138828269045763169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24725915036875384122035117 9272218138828269045763169)
      ·
        refine ⟨6954163604121201784322377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9272218138828269045763169 6954163604121201784322377)
        ·
          refine ⟨5215622703090901338241783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6954163604121201784322377 5215622703090901338241783)
          ·
            refine ⟨7823434054636352007362675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215622703090901338241783 7823434054636352007362675)
            ·
              refine ⟨11735151081954528011044013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823434054636352007362675 11735151081954528011044013)
              ·
                refine ⟨4400681655732948004141505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11735151081954528011044013 4400681655732948004141505)
                ·
                  refine ⟨3300511241799711003106129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4400681655732948004141505 3300511241799711003106129)
                  ·
                    refine ⟨2475383431349783252329597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3300511241799711003106129 2475383431349783252329597)
                    ·
                      refine ⟨928268786756168719623599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2475383431349783252329597 928268786756168719623599)
                      ·
                        rfl

theorem cell23_1807797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1807797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807797 prefixEnd_1807797 := by exact prefixLift 1807797
  have htrace : WordTrace (prefixWord ++ tailWord_1807797) baseStart_1807797 baseEnd_1807797 := by
    simpa [prefixWord, tailWord_1807797, baseEnd_1807797] using wordTrace_append hprefix tailTrace_1807797
  have hstable : (prefixWord ++ tailWord_1807797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807797).length < 2 ^ (prefixWord ++ tailWord_1807797).sum := by decide
  have hdescent : baseEnd_1807797 < baseStart_1807797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807864 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 1, 5]
def baseStart_1807864 : Nat := 118140960795 + 1807864 * 2 ^ 59
def prefixEnd_1807864 : Nat := 4983230072969 + 3 ^ 40 * 1807864 * 2
def baseEnd_1807864 : Nat := 309434396653339985828597

theorem tailTrace_1807864 : CollatzResearch.WordTrace tailWord_1807864 prefixEnd_1807864 309434396653339985828597 := by
  unfold tailWord_1807864
  simp only [CollatzResearch.WordTrace]
  refine ⟨32969108561212480717391323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43958811414949974289855097 32969108561212480717391323)
  ·
    refine ⟨49453662841818721076086985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32969108561212480717391323 49453662841818721076086985)
    ·
      refine ⟨37090247131364040807065239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49453662841818721076086985 37090247131364040807065239)
      ·
        refine ⟨55635370697046061210597859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37090247131364040807065239 55635370697046061210597859)
        ·
          refine ⟨83453056045569091815896789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55635370697046061210597859 83453056045569091815896789)
          ·
            refine ⟨1955931001068025589435081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 83453056045569091815896789 1955931001068025589435081)
            ·
              refine ⟨1466948250801019192076311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955931001068025589435081 1466948250801019192076311)
              ·
                refine ⟨2200422376201528788114467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466948250801019192076311 2200422376201528788114467)
                ·
                  refine ⟨3300633564302293182171701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200422376201528788114467 3300633564302293182171701)
                  ·
                    refine ⟨309434396653339985828597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3300633564302293182171701 309434396653339985828597)
                    ·
                      rfl

theorem cell23_1807864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_1807864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807864 prefixEnd_1807864 := by exact prefixLift 1807864
  have htrace : WordTrace (prefixWord ++ tailWord_1807864) baseStart_1807864 baseEnd_1807864 := by
    simpa [prefixWord, tailWord_1807864, baseEnd_1807864] using wordTrace_append hprefix tailTrace_1807864
  have hstable : (prefixWord ++ tailWord_1807864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807864).length < 2 ^ (prefixWord ++ tailWord_1807864).sum := by decide
  have hdescent : baseEnd_1807864 < baseStart_1807864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807880 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1807880 : Nat := 118140960795 + 1807880 * 2 ^ 59
def prefixEnd_1807880 : Nat := 4983230072969 + 3 ^ 40 * 1807880 * 2
def baseEnd_1807880 : Nat := 928311405650491894885717

theorem tailTrace_1807880 : CollatzResearch.WordTrace tailWord_1807880 prefixEnd_1807880 928311405650491894885717 := by
  unfold tailWord_1807880
  simp only [CollatzResearch.WordTrace]
  refine ⟨32969400345183498083682547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43959200460244664111576729 32969400345183498083682547)
  ·
    refine ⟨49454100517775247125523821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32969400345183498083682547 49454100517775247125523821)
    ·
      refine ⟨18545287694165717672071433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49454100517775247125523821 18545287694165717672071433)
      ·
        refine ⟨13908965770624288254053575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18545287694165717672071433 13908965770624288254053575)
        ·
          refine ⟨20863448655936432381080363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13908965770624288254053575 20863448655936432381080363)
          ·
            refine ⟨31295172983904648571620545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20863448655936432381080363 31295172983904648571620545)
            ·
              refine ⟨23471379737928486428715409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31295172983904648571620545 23471379737928486428715409)
              ·
                refine ⟨17603534803446364821536557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23471379737928486428715409 17603534803446364821536557)
                ·
                  refine ⟨6601325551292386808076209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17603534803446364821536557 6601325551292386808076209)
                  ·
                    refine ⟨4950994163469290106057157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6601325551292386808076209 4950994163469290106057157)
                    ·
                      refine ⟨928311405650491894885717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4950994163469290106057157 928311405650491894885717)
                      ·
                        rfl

theorem cell23_1807880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1807880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807880 prefixEnd_1807880 := by exact prefixLift 1807880
  have htrace : WordTrace (prefixWord ++ tailWord_1807880) baseStart_1807880 baseEnd_1807880 := by
    simpa [prefixWord, tailWord_1807880, baseEnd_1807880] using wordTrace_append hprefix tailTrace_1807880
  have hstable : (prefixWord ++ tailWord_1807880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807880).length < 2 ^ (prefixWord ++ tailWord_1807880).sum := by decide
  have hdescent : baseEnd_1807880 < baseStart_1807880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807904 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1807904 : Nat := 118140960795 + 1807904 * 2 ^ 59
def prefixEnd_1807904 : Nat := 4983230072969 + 3 ^ 40 * 1807904 * 2
def baseEnd_1807904 : Nat := 928323729186199800985607

theorem tailTrace_1807904 : CollatzResearch.WordTrace tailWord_1807904 prefixEnd_1807904 928323729186199800985607 := by
  unfold tailWord_1807904
  simp only [CollatzResearch.WordTrace]
  refine ⟨32969838021140024133119383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43959784028186698844159177 32969838021140024133119383)
  ·
    refine ⟨49454757031710036199679075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32969838021140024133119383 49454757031710036199679075)
    ·
      refine ⟨74182135547565054299518613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49454757031710036199679075 74182135547565054299518613)
      ·
        refine ⟨3477287603792111920289935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74182135547565054299518613 3477287603792111920289935)
        ·
          refine ⟨5215931405688167880434903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3477287603792111920289935 5215931405688167880434903)
          ·
            refine ⟨7823897108532251820652355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215931405688167880434903 7823897108532251820652355)
            ·
              refine ⟨11735845662798377730978533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823897108532251820652355 11735845662798377730978533)
              ·
                refine ⟨2200471061774695824558475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11735845662798377730978533 2200471061774695824558475)
                ·
                  refine ⟨3300706592662043736837713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200471061774695824558475 3300706592662043736837713)
                  ·
                    refine ⟨2475529944496532802628285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3300706592662043736837713 2475529944496532802628285)
                    ·
                      refine ⟨928323729186199800985607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2475529944496532802628285 928323729186199800985607)
                      ·
                        rfl

theorem cell23_1807904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1807904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807904 prefixEnd_1807904 := by exact prefixLift 1807904
  have htrace : WordTrace (prefixWord ++ tailWord_1807904) baseStart_1807904 baseEnd_1807904 := by
    simpa [prefixWord, tailWord_1807904, baseEnd_1807904] using wordTrace_append hprefix tailTrace_1807904
  have hstable : (prefixWord ++ tailWord_1807904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807904).length < 2 ^ (prefixWord ++ tailWord_1807904).sum := by decide
  have hdescent : baseEnd_1807904 < baseStart_1807904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807930 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_1807930 : Nat := 118140960795 + 1807930 * 2 ^ 59
def prefixEnd_1807930 : Nat := 4983230072969 + 3 ^ 40 * 1807930 * 2
def baseEnd_1807930 : Nat := 928337079683216699260487

theorem tailTrace_1807930 : CollatzResearch.WordTrace tailWord_1807930 prefixEnd_1807930 928337079683216699260487 := by
  unfold tailWord_1807930
  simp only [CollatzResearch.WordTrace]
  refine ⟨16485156085046463676671311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43960416226790569804456829 16485156085046463676671311)
  ·
    refine ⟨24727734127569695515006967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16485156085046463676671311 24727734127569695515006967)
    ·
      refine ⟨37091601191354543272510451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24727734127569695515006967 37091601191354543272510451)
      ·
        refine ⟨55637401787031814908765677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37091601191354543272510451 55637401787031814908765677)
        ·
          refine ⟨20864025670136930590787129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55637401787031814908765677 20864025670136930590787129)
          ·
            refine ⟨15648019252602697943090347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20864025670136930590787129 15648019252602697943090347)
            ·
              refine ⟨23472028878904046914635521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15648019252602697943090347 23472028878904046914635521)
              ·
                refine ⟨17604021659178035185976641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23472028878904046914635521 17604021659178035185976641)
                ·
                  refine ⟨13203016244383526389482481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17604021659178035185976641 13203016244383526389482481)
                  ·
                    refine ⟨9902262183287644792111861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13203016244383526389482481 9902262183287644792111861)
                    ·
                      refine ⟨928337079683216699260487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9902262183287644792111861 928337079683216699260487)
                      ·
                        rfl

theorem cell23_1807930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_1807930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807930 prefixEnd_1807930 := by exact prefixLift 1807930
  have htrace : WordTrace (prefixWord ++ tailWord_1807930) baseStart_1807930 baseEnd_1807930 := by
    simpa [prefixWord, tailWord_1807930, baseEnd_1807930] using wordTrace_append hprefix tailTrace_1807930
  have hstable : (prefixWord ++ tailWord_1807930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807930).length < 2 ^ (prefixWord ++ tailWord_1807930).sum := by decide
  have hdescent : baseEnd_1807930 < baseStart_1807930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807950 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_1807950 : Nat := 118140960795 + 1807950 * 2 ^ 59
def prefixEnd_1807950 : Nat := 4983230072969 + 3 ^ 40 * 1807950 * 2
def baseEnd_1807950 : Nat := 309449116432102207003465

theorem tailTrace_1807950 : CollatzResearch.WordTrace tailWord_1807950 prefixEnd_1807950 309449116432102207003465 := by
  unfold tailWord_1807950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8242669225014174765301663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43960902533408932081608869 8242669225014174765301663)
  ·
    refine ⟨12364003837521262147952495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8242669225014174765301663 12364003837521262147952495)
    ·
      refine ⟨18546005756281893221928743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12364003837521262147952495 18546005756281893221928743)
      ·
        refine ⟨27819008634422839832893115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18546005756281893221928743 27819008634422839832893115)
        ·
          refine ⟨41728512951634259749339673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27819008634422839832893115 41728512951634259749339673)
          ·
            refine ⟨31296384713725694812004755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41728512951634259749339673 31296384713725694812004755)
            ·
              refine ⟨46944577070588542218007133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31296384713725694812004755 46944577070588542218007133)
              ·
                refine ⟨17604216401470703331752675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46944577070588542218007133 17604216401470703331752675)
                ·
                  refine ⟨26406324602206054997629013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17604216401470703331752675 26406324602206054997629013)
                  ·
                    refine ⟨309449116432102207003465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26406324602206054997629013 309449116432102207003465)
                    ·
                      rfl

theorem cell23_1807950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_1807950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807950 prefixEnd_1807950 := by exact prefixLift 1807950
  have htrace : WordTrace (prefixWord ++ tailWord_1807950) baseStart_1807950 baseEnd_1807950 := by
    simpa [prefixWord, tailWord_1807950, baseEnd_1807950] using wordTrace_append hprefix tailTrace_1807950
  have hstable : (prefixWord ++ tailWord_1807950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807950).length < 2 ^ (prefixWord ++ tailWord_1807950).sum := by decide
  have hdescent : baseEnd_1807950 < baseStart_1807950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1807978 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_1807978 : Nat := 118140960795 + 1807978 * 2 ^ 59
def prefixEnd_1807978 : Nat := 4983230072969 + 3 ^ 40 * 1807978 * 2
def baseEnd_1807978 : Nat := 928361726754632511460267

theorem tailTrace_1807978 : CollatzResearch.WordTrace tailWord_1807978 prefixEnd_1807978 928361726754632511460267 := by
  unfold tailWord_1807978
  simp only [CollatzResearch.WordTrace]
  refine ⟨16485593761002989726108147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43961583362674639269621725 16485593761002989726108147)
  ·
    refine ⟨24728390641504484589162221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16485593761002989726108147 24728390641504484589162221)
    ·
      refine ⟨9273146490564181720935833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24728390641504484589162221 9273146490564181720935833)
      ·
        refine ⟨6954859867923136290701875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9273146490564181720935833 6954859867923136290701875)
        ·
          refine ⟨10432289801884704436052813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6954859867923136290701875 10432289801884704436052813)
          ·
            refine ⟨3912108675706764163519805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10432289801884704436052813 3912108675706764163519805)
            ·
              refine ⟨1467040753390036561319927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3912108675706764163519805 1467040753390036561319927)
              ·
                refine ⟨2200561130085054841979891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467040753390036561319927 2200561130085054841979891)
                ·
                  refine ⟨3300841695127582262969837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200561130085054841979891 3300841695127582262969837)
                  ·
                    refine ⟨1237815635672843348613689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3300841695127582262969837 1237815635672843348613689)
                    ·
                      refine ⟨928361726754632511460267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1237815635672843348613689 928361726754632511460267)
                      ·
                        rfl

theorem cell23_1807978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_1807978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1807978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1807978 prefixEnd_1807978 := by exact prefixLift 1807978
  have htrace : WordTrace (prefixWord ++ tailWord_1807978) baseStart_1807978 baseEnd_1807978 := by
    simpa [prefixWord, tailWord_1807978, baseEnd_1807978] using wordTrace_append hprefix tailTrace_1807978
  have hstable : (prefixWord ++ tailWord_1807978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1807978).length < 2 ^ (prefixWord ++ tailWord_1807978).sum := by decide
  have hdescent : baseEnd_1807978 < baseStart_1807978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1807978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808004 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1808004 : Nat := 118140960795 + 1808004 * 2 ^ 59
def prefixEnd_1808004 : Nat := 4983230072969 + 3 ^ 40 * 1808004 * 2
def baseEnd_1808004 : Nat := 928375077251649409735147

theorem tailTrace_1808004 : CollatzResearch.WordTrace tailWord_1808004 prefixEnd_1808004 928375077251649409735147 := by
  unfold tailWord_1808004
  simp only [CollatzResearch.WordTrace]
  refine ⟨32971661670958882672439533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43962215561278510229919377 32971661670958882672439533)
  ·
    refine ⟨12364373126609581002164825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32971661670958882672439533 12364373126609581002164825)
    ·
      refine ⟨9273279844957185751623619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12364373126609581002164825 9273279844957185751623619)
      ·
        refine ⟨13909919767435778627435429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9273279844957185751623619 13909919767435778627435429)
        ·
          refine ⟨2608109956394208492644143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13909919767435778627435429 2608109956394208492644143)
          ·
            refine ⟨3912164934591312738966215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608109956394208492644143 3912164934591312738966215)
            ·
              refine ⟨5868247401886969108449323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3912164934591312738966215 5868247401886969108449323)
              ·
                refine ⟨8802371102830453662673985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5868247401886969108449323 8802371102830453662673985)
                ·
                  refine ⟨6601778327122840247005489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8802371102830453662673985 6601778327122840247005489)
                  ·
                    refine ⟨4951333745342130185254117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6601778327122840247005489 4951333745342130185254117)
                    ·
                      refine ⟨928375077251649409735147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4951333745342130185254117 928375077251649409735147)
                      ·
                        rfl

theorem cell23_1808004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1808004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808004 prefixEnd_1808004 := by exact prefixLift 1808004
  have htrace : WordTrace (prefixWord ++ tailWord_1808004) baseStart_1808004 baseEnd_1808004 := by
    simpa [prefixWord, tailWord_1808004, baseEnd_1808004] using wordTrace_append hprefix tailTrace_1808004
  have hstable : (prefixWord ++ tailWord_1808004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808004).length < 2 ^ (prefixWord ++ tailWord_1808004).sum := by decide
  have hdescent : baseEnd_1808004 < baseStart_1808004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808007 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_1808007 : Nat := 118140960795 + 1808007 * 2 ^ 59
def prefixEnd_1808007 : Nat := 4983230072969 + 3 ^ 40 * 1808007 * 2
def baseEnd_1808007 : Nat := 928376617693612897997633

theorem tailTrace_1808007 : CollatzResearch.WordTrace tailWord_1808007 prefixEnd_1808007 928376617693612897997633 := by
  unfold tailWord_1808007
  simp only [CollatzResearch.WordTrace]
  refine ⟨65943432760906896857238275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43962288507271264571492183 65943432760906896857238275)
  ·
    refine ⟨98915149141360345285857413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65943432760906896857238275 98915149141360345285857413)
    ·
      refine ⟨18546590464005064741098265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98915149141360345285857413 18546590464005064741098265)
      ·
        refine ⟨13909942848003798555823699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18546590464005064741098265 13909942848003798555823699)
        ·
          refine ⟨20864914272005697833735549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13909942848003798555823699 20864914272005697833735549)
          ·
            refine ⟨7824342852002136687650831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20864914272005697833735549 7824342852002136687650831)
            ·
              refine ⟨11736514278003205031476247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7824342852002136687650831 11736514278003205031476247)
              ·
                refine ⟨17604771417004807547214371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11736514278003205031476247 17604771417004807547214371)
                ·
                  refine ⟨26407157125507211320821557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17604771417004807547214371 26407157125507211320821557)
                  ·
                    refine ⟨2475670980516301061327021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26407157125507211320821557 2475670980516301061327021)
                    ·
                      refine ⟨928376617693612897997633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2475670980516301061327021 928376617693612897997633)
                      ·
                        rfl

theorem cell23_1808007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_1808007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808007 prefixEnd_1808007 := by exact prefixLift 1808007
  have htrace : WordTrace (prefixWord ++ tailWord_1808007) baseStart_1808007 baseEnd_1808007 := by
    simpa [prefixWord, tailWord_1808007, baseEnd_1808007] using wordTrace_append hprefix tailTrace_1808007
  have hstable : (prefixWord ++ tailWord_1808007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808007).length < 2 ^ (prefixWord ++ tailWord_1808007).sum := by decide
  have hdescent : baseEnd_1808007 < baseStart_1808007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808008 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1808008 : Nat := 118140960795 + 1808008 * 2 ^ 59
def prefixEnd_1808008 : Nat := 4983230072969 + 3 ^ 40 * 1808008 * 2
def baseEnd_1808008 : Nat := 928377131174267394085129

theorem tailTrace_1808008 : CollatzResearch.WordTrace tailWord_1808008 prefixEnd_1808008 928377131174267394085129 := by
  unfold tailWord_1808008
  simp only [CollatzResearch.WordTrace]
  refine ⟨32971734616951637014012339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43962312822602182685349785 32971734616951637014012339)
  ·
    refine ⟨49457601925427455521018509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32971734616951637014012339 49457601925427455521018509)
    ·
      refine ⟨18546600722035295820381941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49457601925427455521018509 18546600722035295820381941)
      ·
        refine ⟨1738743817690808983160807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18546600722035295820381941 1738743817690808983160807)
        ·
          refine ⟨2608115726536213474741211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738743817690808983160807 2608115726536213474741211)
          ·
            refine ⟨3912173589804320212111817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608115726536213474741211 3912173589804320212111817)
            ·
              refine ⟨2934130192353240159083863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3912173589804320212111817 2934130192353240159083863)
              ·
                refine ⟨4401195288529860238625795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934130192353240159083863 4401195288529860238625795)
                ·
                  refine ⟨6601792932794790357938693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401195288529860238625795 6601792932794790357938693)
                  ·
                    refine ⟨1237836174899023192113505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6601792932794790357938693 1237836174899023192113505)
                    ·
                      refine ⟨928377131174267394085129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1237836174899023192113505 928377131174267394085129)
                      ·
                        rfl

theorem cell23_1808008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1808008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808008 prefixEnd_1808008 := by exact prefixLift 1808008
  have htrace : WordTrace (prefixWord ++ tailWord_1808008) baseStart_1808008 baseEnd_1808008 := by
    simpa [prefixWord, tailWord_1808008, baseEnd_1808008] using wordTrace_append hprefix tailTrace_1808008
  have hstable : (prefixWord ++ tailWord_1808008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808008).length < 2 ^ (prefixWord ++ tailWord_1808008).sum := by decide
  have hdescent : baseEnd_1808008 < baseStart_1808008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808047 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_1808047 : Nat := 118140960795 + 1808047 * 2 ^ 59
def prefixEnd_1808047 : Nat := 4983230072969 + 3 ^ 40 * 1808047 * 2
def baseEnd_1808047 : Nat := 928397156919792741497449

theorem tailTrace_1808047 : CollatzResearch.WordTrace tailWord_1808047 prefixEnd_1808047 928397156919792741497449 := by
  unfold tailWord_1808047
  simp only [CollatzResearch.WordTrace]
  refine ⟨65944891680761983688694395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43963261120507989125796263 65944891680761983688694395)
  ·
    refine ⟨98917337521142975533041593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65944891680761983688694395 98917337521142975533041593)
    ·
      refine ⟨74188003140857231649781195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98917337521142975533041593 74188003140857231649781195)
      ·
        refine ⟨111282004711285847474671793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74188003140857231649781195 111282004711285847474671793)
        ·
          refine ⟨83461503533464385606003845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111282004711285847474671793 83461503533464385606003845)
          ·
            refine ⟨15649031912524572301125721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83461503533464385606003845 15649031912524572301125721)
            ·
              refine ⟨11736773934393429225844291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15649031912524572301125721 11736773934393429225844291)
              ·
                refine ⟨17605160901590143838766437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11736773934393429225844291 17605160901590143838766437)
                ·
                  refine ⟨3300967669048151969768707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17605160901590143838766437 3300967669048151969768707)
                  ·
                    refine ⟨4951451503572227954653061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3300967669048151969768707 4951451503572227954653061)
                    ·
                      refine ⟨928397156919792741497449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4951451503572227954653061 928397156919792741497449)
                      ·
                        rfl

theorem cell23_1808047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_1808047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808047 prefixEnd_1808047 := by exact prefixLift 1808047
  have htrace : WordTrace (prefixWord ++ tailWord_1808047) baseStart_1808047 baseEnd_1808047 := by
    simpa [prefixWord, tailWord_1808047, baseEnd_1808047] using wordTrace_append hprefix tailTrace_1808047
  have hstable : (prefixWord ++ tailWord_1808047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808047).length < 2 ^ (prefixWord ++ tailWord_1808047).sum := by decide
  have hdescent : baseEnd_1808047 < baseStart_1808047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808064 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 2, 4, 2]
def baseStart_1808064 : Nat := 118140960795 + 1808064 * 2 ^ 59
def prefixEnd_1808064 : Nat := 4983230072969 + 3 ^ 40 * 1808064 * 2
def baseEnd_1808064 : Nat := 928405886090919174984871

theorem tailTrace_1808064 : CollatzResearch.WordTrace tailWord_1808064 prefixEnd_1808064 928405886090919174984871 := by
  unfold tailWord_1808064
  simp only [CollatzResearch.WordTrace]
  refine ⟨32972755860850197796031623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43963674481133597061375497 32972755860850197796031623)
  ·
    refine ⟨49459133791275296694047435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32972755860850197796031623 49459133791275296694047435)
    ·
      refine ⟨74188700686912945041071153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49459133791275296694047435 74188700686912945041071153)
      ·
        refine ⟨55641525515184708780803365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74188700686912945041071153 55641525515184708780803365)
        ·
          refine ⟨10432786034097132896400631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55641525515184708780803365 10432786034097132896400631)
          ·
            refine ⟨15649179051145699344600947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10432786034097132896400631 15649179051145699344600947)
            ·
              refine ⟨23473768576718549016901421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15649179051145699344600947 23473768576718549016901421)
              ·
                refine ⟨8802663216269455881338033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23473768576718549016901421 8802663216269455881338033)
                ·
                  refine ⟨6601997412202091911003525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8802663216269455881338033 6601997412202091911003525)
                  ·
                    refine ⟨1237874514787892233313161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6601997412202091911003525 1237874514787892233313161)
                    ·
                      refine ⟨928405886090919174984871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1237874514787892233313161 928405886090919174984871)
                      ·
                        rfl

theorem cell23_1808064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_1808064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808064 prefixEnd_1808064 := by exact prefixLift 1808064
  have htrace : WordTrace (prefixWord ++ tailWord_1808064) baseStart_1808064 baseEnd_1808064 := by
    simpa [prefixWord, tailWord_1808064, baseEnd_1808064] using wordTrace_append hprefix tailTrace_1808064
  have hstable : (prefixWord ++ tailWord_1808064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808064).length < 2 ^ (prefixWord ++ tailWord_1808064).sum := by decide
  have hdescent : baseEnd_1808064 < baseStart_1808064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808165 : List Nat := [1, 3, 1, 2, 3, 2, 4, 2, 1, 1, 3]
def baseStart_1808165 : Nat := 118140960795 + 1808165 * 2 ^ 59
def prefixEnd_1808165 : Nat := 4983230072969 + 3 ^ 40 * 1808165 * 2
def baseEnd_1808165 : Nat := 928457747637023279821907

theorem tailTrace_1808165 : CollatzResearch.WordTrace tailWord_1808165 prefixEnd_1808165 928457747637023279821907 := by
  unfold tailWord_1808165
  simp only [CollatzResearch.WordTrace]
  refine ⟨65949195494334489841489949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43966130329556326560993299 65949195494334489841489949)
  ·
    refine ⟨24730948310375433690558731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65949195494334489841489949 24730948310375433690558731)
    ·
      refine ⟨37096422465563150535838097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24730948310375433690558731 37096422465563150535838097)
      ·
        refine ⟨27822316849172362901878573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37096422465563150535838097 27822316849172362901878573)
        ·
          refine ⟨10433368818439636088204465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27822316849172362901878573 10433368818439636088204465)
          ·
            refine ⟨7825026613829727066153349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10433368818439636088204465 7825026613829727066153349)
            ·
              refine ⟨1467192490093073824903753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7825026613829727066153349 1467192490093073824903753)
              ·
                refine ⟨1100394367569805368677815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467192490093073824903753 1100394367569805368677815)
                ·
                  refine ⟨1650591551354708053016723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100394367569805368677815 1650591551354708053016723)
                  ·
                    refine ⟨2475887327032062079525085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1650591551354708053016723 2475887327032062079525085)
                    ·
                      refine ⟨928457747637023279821907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2475887327032062079525085 928457747637023279821907)
                      ·
                        rfl

theorem cell23_1808165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_1808165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808165 prefixEnd_1808165 := by exact prefixLift 1808165
  have htrace : WordTrace (prefixWord ++ tailWord_1808165) baseStart_1808165 baseEnd_1808165 := by
    simpa [prefixWord, tailWord_1808165, baseEnd_1808165] using wordTrace_append hprefix tailTrace_1808165
  have hstable : (prefixWord ++ tailWord_1808165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808165).length < 2 ^ (prefixWord ++ tailWord_1808165).sum := by decide
  have hdescent : baseEnd_1808165 < baseStart_1808165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808181 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1808181 : Nat := 118140960795 + 1808181 * 2 ^ 59
def prefixEnd_1808181 : Nat := 4983230072969 + 3 ^ 40 * 1808181 * 2
def baseEnd_1808181 : Nat := 309488654442498405740611

theorem tailTrace_1808181 : CollatzResearch.WordTrace tailWord_1808181 prefixEnd_1808181 309488654442498405740611 := by
  unfold tailWord_1808181
  simp only [CollatzResearch.WordTrace]
  refine ⟨65949779062276524574072397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43966519374851016382714931 65949779062276524574072397)
  ·
    refine ⟨24731167148353696715277149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65949779062276524574072397 24731167148353696715277149)
    ·
      refine ⟨9274187680632636268228931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24731167148353696715277149 9274187680632636268228931)
      ·
        refine ⟨13911281520948954402343397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9274187680632636268228931 13911281520948954402343397)
        ·
          refine ⟨2608365285177928950439387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13911281520948954402343397 2608365285177928950439387)
          ·
            refine ⟨3912547927766893425659081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608365285177928950439387 3912547927766893425659081)
            ·
              refine ⟨2934410945825170069244311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3912547927766893425659081 2934410945825170069244311)
              ·
                refine ⟨4401616418737755103866467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934410945825170069244311 4401616418737755103866467)
                ·
                  refine ⟨6602424628106632655799701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401616418737755103866467 6602424628106632655799701)
                  ·
                    refine ⟨309488654442498405740611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6602424628106632655799701 309488654442498405740611)
                    ·
                      rfl

theorem cell23_1808181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1808181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808181 prefixEnd_1808181 := by exact prefixLift 1808181
  have htrace : WordTrace (prefixWord ++ tailWord_1808181) baseStart_1808181 baseEnd_1808181 := by
    simpa [prefixWord, tailWord_1808181, baseEnd_1808181] using wordTrace_append hprefix tailTrace_1808181
  have hstable : (prefixWord ++ tailWord_1808181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808181).length < 2 ^ (prefixWord ++ tailWord_1808181).sum := by decide
  have hdescent : baseEnd_1808181 < baseStart_1808181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808184 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_1808184 : Nat := 118140960795 + 1808184 * 2 ^ 59
def prefixEnd_1808184 : Nat := 4983230072969 + 3 ^ 40 * 1808184 * 2
def baseEnd_1808184 : Nat := 928467503769458705484319

theorem tailTrace_1808184 : CollatzResearch.WordTrace tailWord_1808184 prefixEnd_1808184 928467503769458705484319 := by
  unfold tailWord_1808184
  simp only [CollatzResearch.WordTrace]
  refine ⟨32974944240632828043215803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43966592320843770724287737 32974944240632828043215803)
  ·
    refine ⟨49462416360949242064823705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32974944240632828043215803 49462416360949242064823705)
    ·
      refine ⟨37096812270711931548617779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49462416360949242064823705 37096812270711931548617779)
      ·
        refine ⟨55645218406067897322926669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37096812270711931548617779 55645218406067897322926669)
        ·
          refine ⟨20866956902275461496097501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55645218406067897322926669 20866956902275461496097501)
          ·
            refine ⟨7825108838353298061036563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20866956902275461496097501 7825108838353298061036563)
            ·
              refine ⟨11737663257529947091554845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825108838353298061036563 11737663257529947091554845)
              ·
                refine ⟨4401623721573730159333067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11737663257529947091554845 4401623721573730159333067)
                ·
                  refine ⟨6602435582360595238999601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401623721573730159333067 6602435582360595238999601)
                  ·
                    refine ⟨4951826686770446429249701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6602435582360595238999601 4951826686770446429249701)
                    ·
                      refine ⟨928467503769458705484319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4951826686770446429249701 928467503769458705484319)
                      ·
                        rfl

theorem cell23_1808184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_1808184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808184 prefixEnd_1808184 := by exact prefixLift 1808184
  have htrace : WordTrace (prefixWord ++ tailWord_1808184) baseStart_1808184 baseEnd_1808184 := by
    simpa [prefixWord, tailWord_1808184, baseEnd_1808184] using wordTrace_append hprefix tailTrace_1808184
  have hstable : (prefixWord ++ tailWord_1808184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808184).length < 2 ^ (prefixWord ++ tailWord_1808184).sum := by decide
  have hdescent : baseEnd_1808184 < baseStart_1808184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808198 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1808198 : Nat := 118140960795 + 1808198 * 2 ^ 59
def prefixEnd_1808198 : Nat := 4983230072969 + 3 ^ 40 * 1808198 * 2
def baseEnd_1808198 : Nat := 309491564166207216903085

theorem tailTrace_1808198 : CollatzResearch.WordTrace tailWord_1808198 prefixEnd_1808198 309491564166207216903085 := by
  unfold tailWord_1808198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060949971975466764920039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43966932735476624318294165 2060949971975466764920039)
  ·
    refine ⟨3091424957963200147380059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060949971975466764920039 3091424957963200147380059)
    ·
      refine ⟨4637137436944800221070089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091424957963200147380059 4637137436944800221070089)
      ·
        refine ⟨3477853077708600165802567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4637137436944800221070089 3477853077708600165802567)
        ·
          refine ⟨5216779616562900248703851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3477853077708600165802567 5216779616562900248703851)
          ·
            refine ⟨7825169424844350373055777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216779616562900248703851 7825169424844350373055777)
            ·
              refine ⟨5868877068633262779791833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7825169424844350373055777 5868877068633262779791833)
              ·
                refine ⟨4401657801474947084843875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5868877068633262779791833 4401657801474947084843875)
                ·
                  refine ⟨6602486702212420627265813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401657801474947084843875 6602486702212420627265813)
                  ·
                    refine ⟨309491564166207216903085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6602486702212420627265813 309491564166207216903085)
                    ·
                      rfl

theorem cell23_1808198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1808198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808198 prefixEnd_1808198 := by exact prefixLift 1808198
  have htrace : WordTrace (prefixWord ++ tailWord_1808198) baseStart_1808198 baseEnd_1808198 := by
    simpa [prefixWord, tailWord_1808198, baseEnd_1808198] using wordTrace_append hprefix tailTrace_1808198
  have hstable : (prefixWord ++ tailWord_1808198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808198).length < 2 ^ (prefixWord ++ tailWord_1808198).sum := by decide
  have hdescent : baseEnd_1808198 < baseStart_1808198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808205 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_1808205 : Nat := 118140960795 + 1808205 * 2 ^ 59
def prefixEnd_1808205 : Nat := 4983230072969 + 3 ^ 40 * 1808205 * 2
def baseEnd_1808205 : Nat := 928478286863203123321723

theorem tailTrace_1808205 : CollatzResearch.WordTrace tailWord_1808205 prefixEnd_1808205 928478286863203123321723 := by
  unfold tailWord_1808205
  simp only [CollatzResearch.WordTrace]
  refine ⟨65950654414189576672946069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43967102942793051115297379 65950654414189576672946069)
  ·
    refine ⟨3091436925665136406544347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65950654414189576672946069 3091436925665136406544347)
    ·
      refine ⟨4637155388497704609816521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091436925665136406544347 4637155388497704609816521)
      ·
        refine ⟨3477866541373278457362391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4637155388497704609816521 3477866541373278457362391)
        ·
          refine ⟨5216799812059917686043587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3477866541373278457362391 5216799812059917686043587)
          ·
            refine ⟨7825199718089876529065381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216799812059917686043587 7825199718089876529065381)
            ·
              refine ⟨1467224947141851849199759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7825199718089876529065381 1467224947141851849199759)
              ·
                refine ⟨2200837420712777773799639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467224947141851849199759 2200837420712777773799639)
                ·
                  refine ⟨3301256131069166660699459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200837420712777773799639 3301256131069166660699459)
                  ·
                    refine ⟨4951884196603749991049189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3301256131069166660699459 4951884196603749991049189)
                    ·
                      refine ⟨928478286863203123321723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4951884196603749991049189 928478286863203123321723)
                      ·
                        rfl

theorem cell23_1808205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_1808205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808205 prefixEnd_1808205 := by exact prefixLift 1808205
  have htrace : WordTrace (prefixWord ++ tailWord_1808205) baseStart_1808205 baseEnd_1808205 := by
    simpa [prefixWord, tailWord_1808205, baseEnd_1808205] using wordTrace_append hprefix tailTrace_1808205
  have hstable : (prefixWord ++ tailWord_1808205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808205).length < 2 ^ (prefixWord ++ tailWord_1808205).sum := by decide
  have hdescent : baseEnd_1808205 < baseStart_1808205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808215 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 2, 4]
def baseStart_1808215 : Nat := 118140960795 + 1808215 * 2 ^ 59
def prefixEnd_1808215 : Nat := 4983230072969 + 3 ^ 40 * 1808215 * 2
def baseEnd_1808215 : Nat := 309494473889916028065559

theorem tailTrace_1808215 : CollatzResearch.WordTrace tailWord_1808215 prefixEnd_1808215 309494473889916028065559 := by
  unfold tailWord_1808215
  simp only [CollatzResearch.WordTrace]
  refine ⟨65951019144153348380810099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43967346096102232253873399 65951019144153348380810099)
  ·
    refine ⟨98926528716230022571215149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65951019144153348380810099 98926528716230022571215149)
    ·
      refine ⟨37097448268586258464205681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98926528716230022571215149 37097448268586258464205681)
      ·
        refine ⟨27823086201439693848154261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37097448268586258464205681 27823086201439693848154261)
        ·
          refine ⟨1304207165692485649132231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27823086201439693848154261 1304207165692485649132231)
          ·
            refine ⟨1956310748538728473698347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304207165692485649132231 1956310748538728473698347)
            ·
              refine ⟨2934466122808092710547521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956310748538728473698347 2934466122808092710547521)
              ·
                refine ⟨2200849592106069532910641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2934466122808092710547521 2200849592106069532910641)
                ·
                  refine ⟨1650637194079552149682981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2200849592106069532910641 1650637194079552149682981)
                  ·
                    refine ⟨309494473889916028065559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1650637194079552149682981 309494473889916028065559)
                    ·
                      rfl

theorem cell23_1808215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_1808215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808215 prefixEnd_1808215 := by exact prefixLift 1808215
  have htrace : WordTrace (prefixWord ++ tailWord_1808215) baseStart_1808215 baseEnd_1808215 := by
    simpa [prefixWord, tailWord_1808215, baseEnd_1808215] using wordTrace_append hprefix tailTrace_1808215
  have hstable : (prefixWord ++ tailWord_1808215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808215).length < 2 ^ (prefixWord ++ tailWord_1808215).sum := by decide
  have hdescent : baseEnd_1808215 < baseStart_1808215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808238 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1808238 : Nat := 118140960795 + 1808238 * 2 ^ 59
def prefixEnd_1808238 : Nat := 4983230072969 + 3 ^ 40 * 1808238 * 2
def baseEnd_1808238 : Nat := 928495231724801494209071

theorem tailTrace_1808238 : CollatzResearch.WordTrace tailWord_1808238 prefixEnd_1808238 928495231724801494209071 := by
  unfold tailWord_1808238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8243982252883752913612171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43967905348713348872598245 8243982252883752913612171)
  ·
    refine ⟨12365973379325629370418257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8243982252883752913612171 12365973379325629370418257)
    ·
      refine ⟨9274480034494222027813693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12365973379325629370418257 9274480034494222027813693)
      ·
        refine ⟨3477930012935333260430135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9274480034494222027813693 3477930012935333260430135)
        ·
          refine ⟨5216895019402999890645203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3477930012935333260430135 5216895019402999890645203)
          ·
            refine ⟨7825342529104499835967805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5216895019402999890645203 7825342529104499835967805)
            ·
              refine ⟨2934503448414187438487927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7825342529104499835967805 2934503448414187438487927)
              ·
                refine ⟨4401755172621281157731891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934503448414187438487927 4401755172621281157731891)
                ·
                  refine ⟨6602632758931921736597837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401755172621281157731891 6602632758931921736597837)
                  ·
                    refine ⟨2475987284599470651224189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6602632758931921736597837 2475987284599470651224189)
                    ·
                      refine ⟨928495231724801494209071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2475987284599470651224189 928495231724801494209071)
                      ·
                        rfl

theorem cell23_1808238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1808238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808238 prefixEnd_1808238 := by exact prefixLift 1808238
  have htrace : WordTrace (prefixWord ++ tailWord_1808238) baseStart_1808238 baseEnd_1808238 := by
    simpa [prefixWord, tailWord_1808238, baseEnd_1808238] using wordTrace_append hprefix tailTrace_1808238
  have hstable : (prefixWord ++ tailWord_1808238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808238).length < 2 ^ (prefixWord ++ tailWord_1808238).sum := by decide
  have hdescent : baseEnd_1808238 < baseStart_1808238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808261 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 3, 4, 2]
def baseStart_1808261 : Nat := 118140960795 + 1808261 * 2 ^ 59
def prefixEnd_1808261 : Nat := 4983230072969 + 3 ^ 40 * 1808261 * 2
def baseEnd_1808261 : Nat := 928507041779854904221465

theorem tailTrace_1808261 : CollatzResearch.WordTrace tailWord_1808261 prefixEnd_1808261 928507041779854904221465 := by
  unfold tailWord_1808261
  simp only [CollatzResearch.WordTrace]
  refine ⟨65952696901986698236984637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43968464601324465491323091 65952696901986698236984637)
  ·
    refine ⟨24732261338245011838869239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65952696901986698236984637 24732261338245011838869239)
    ·
      refine ⟨37098392007367517758303859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24732261338245011838869239 37098392007367517758303859)
      ·
        refine ⟨55647588011051276637455789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37098392007367517758303859 55647588011051276637455789)
        ·
          refine ⟨20867845504144228739045921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55647588011051276637455789 20867845504144228739045921)
          ·
            refine ⟨15650884128108171554284441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20867845504144228739045921 15650884128108171554284441)
            ·
              refine ⟨11738163096081128665713331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15650884128108171554284441 11738163096081128665713331)
              ·
                refine ⟨17607244644121692998569997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11738163096081128665713331 17607244644121692998569997)
                ·
                  refine ⟨6602716741545634874463749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17607244644121692998569997 6602716741545634874463749)
                  ·
                    refine ⟨1238009389039806538961953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6602716741545634874463749 1238009389039806538961953)
                    ·
                      refine ⟨928507041779854904221465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1238009389039806538961953 928507041779854904221465)
                      ·
                        rfl

theorem cell23_1808261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_1808261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808261 prefixEnd_1808261 := by exact prefixLift 1808261
  have htrace : WordTrace (prefixWord ++ tailWord_1808261) baseStart_1808261 baseEnd_1808261 := by
    simpa [prefixWord, tailWord_1808261, baseEnd_1808261] using wordTrace_append hprefix tailTrace_1808261
  have hstable : (prefixWord ++ tailWord_1808261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808261).length < 2 ^ (prefixWord ++ tailWord_1808261).sum := by decide
  have hdescent : baseEnd_1808261 < baseStart_1808261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808289 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1808289 : Nat := 118140960795 + 1808289 * 2 ^ 59
def prefixEnd_1808289 : Nat := 4983230072969 + 3 ^ 40 * 1808289 * 2
def baseEnd_1808289 : Nat := 928521419238180794671337

theorem tailTrace_1808289 : CollatzResearch.WordTrace tailWord_1808289 prefixEnd_1808289 928521419238180794671337 := by
  unfold tailWord_1808289
  simp only [CollatzResearch.WordTrace]
  refine ⟨65953718145885259019003921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43969145430590172679335947 65953718145885259019003921)
  ·
    refine ⟨49465288609413944264252941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65953718145885259019003921 49465288609413944264252941)
    ·
      refine ⟨18549483228530229099094853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49465288609413944264252941 18549483228530229099094853)
      ·
        refine ⟨3478028105349417956080285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18549483228530229099094853 3478028105349417956080285)
        ·
          refine ⟨1304260539506031733530107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3478028105349417956080285 1304260539506031733530107)
          ·
            refine ⟨1956390809259047600295161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304260539506031733530107 1956390809259047600295161)
            ·
              refine ⟨1467293106944285700221371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956390809259047600295161 1467293106944285700221371)
              ·
                refine ⟨2200939660416428550332057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467293106944285700221371 2200939660416428550332057)
                ·
                  refine ⟨1650704745312321412749043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2200939660416428550332057 1650704745312321412749043)
                  ·
                    refine ⟨2476057117968482119123565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1650704745312321412749043 2476057117968482119123565)
                    ·
                      refine ⟨928521419238180794671337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2476057117968482119123565 928521419238180794671337)
                      ·
                        rfl

theorem cell23_1808289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1808289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808289 prefixEnd_1808289 := by exact prefixLift 1808289
  have htrace : WordTrace (prefixWord ++ tailWord_1808289) baseStart_1808289 baseEnd_1808289 := by
    simpa [prefixWord, tailWord_1808289, baseEnd_1808289] using wordTrace_append hprefix tailTrace_1808289
  have hstable : (prefixWord ++ tailWord_1808289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808289).length < 2 ^ (prefixWord ++ tailWord_1808289).sum := by decide
  have hdescent : baseEnd_1808289 < baseStart_1808289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808341 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1808341 : Nat := 118140960795 + 1808341 * 2 ^ 59
def prefixEnd_1808341 : Nat := 4983230072969 + 3 ^ 40 * 1808341 * 2
def baseEnd_1808341 : Nat := 928548120232214591221097

theorem tailTrace_1808341 : CollatzResearch.WordTrace tailWord_1808341 prefixEnd_1808341 928548120232214591221097 := by
  unfold tailWord_1808341
  simp only [CollatzResearch.WordTrace]
  refine ⟨65955614741696871899896877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43970409827797914599931251 65955614741696871899896877)
  ·
    refine ⟨24733355528136326962461329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65955614741696871899896877 24733355528136326962461329)
    ·
      refine ⟨18550016646102245221845997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24733355528136326962461329 18550016646102245221845997)
      ·
        refine ⟨6956256242288341958192249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18550016646102245221845997 6956256242288341958192249)
        ·
          refine ⟨5217192181716256468644187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6956256242288341958192249 5217192181716256468644187)
          ·
            refine ⟨7825788272574384702966281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217192181716256468644187 7825788272574384702966281)
            ·
              refine ⟨5869341204430788527224711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7825788272574384702966281 5869341204430788527224711)
              ·
                refine ⟨8804011806646182790837067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5869341204430788527224711 8804011806646182790837067)
                ·
                  refine ⟨13206017709969274186255601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8804011806646182790837067 13206017709969274186255601)
                  ·
                    refine ⟨9904513282476955639691701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13206017709969274186255601 9904513282476955639691701)
                    ·
                      refine ⟨928548120232214591221097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9904513282476955639691701 928548120232214591221097)
                      ·
                        rfl

theorem cell23_1808341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1808341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808341 prefixEnd_1808341 := by exact prefixLift 1808341
  have htrace : WordTrace (prefixWord ++ tailWord_1808341) baseStart_1808341 baseEnd_1808341 := by
    simpa [prefixWord, tailWord_1808341, baseEnd_1808341] using wordTrace_append hprefix tailTrace_1808341
  have hstable : (prefixWord ++ tailWord_1808341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808341).length < 2 ^ (prefixWord ++ tailWord_1808341).sum := by decide
  have hdescent : baseEnd_1808341 < baseStart_1808341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808364 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_1808364 : Nat := 118140960795 + 1808364 * 2 ^ 59
def prefixEnd_1808364 : Nat := 4983230072969 + 3 ^ 40 * 1808364 * 2
def baseEnd_1808364 : Nat := 928559930287268001233491

theorem tailTrace_1808364 : CollatzResearch.WordTrace tailWord_1808364 prefixEnd_1808364 928559930287268001233491 := by
  unfold tailWord_1808364
  simp only [CollatzResearch.WordTrace]
  refine ⟨32978226810306773413992073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43970969080409031218656097 32978226810306773413992073)
  ·
    refine ⟨24733670107730080060494055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32978226810306773413992073 24733670107730080060494055)
    ·
      refine ⟨37100505161595120090741083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24733670107730080060494055 37100505161595120090741083)
      ·
        refine ⟨55650757742392680136111625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37100505161595120090741083 55650757742392680136111625)
        ·
          refine ⟨41738068306794510102083719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55650757742392680136111625 41738068306794510102083719)
          ·
            refine ⟨62607102460191765153125579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41738068306794510102083719 62607102460191765153125579)
            ·
              refine ⟨93910653690287647729688369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62607102460191765153125579 93910653690287647729688369)
              ·
                refine ⟨70432990267715735797266277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93910653690287647729688369 70432990267715735797266277)
                ·
                  refine ⟨13206185675196700461987427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70432990267715735797266277 13206185675196700461987427)
                  ·
                    refine ⟨19809278512795050692981141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13206185675196700461987427 19809278512795050692981141)
                    ·
                      refine ⟨928559930287268001233491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19809278512795050692981141 928559930287268001233491)
                      ·
                        rfl

theorem cell23_1808364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_1808364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808364 prefixEnd_1808364 := by exact prefixLift 1808364
  have htrace : WordTrace (prefixWord ++ tailWord_1808364) baseStart_1808364 baseEnd_1808364 := by
    simpa [prefixWord, tailWord_1808364, baseEnd_1808364] using wordTrace_append hprefix tailTrace_1808364
  have hstable : (prefixWord ++ tailWord_1808364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808364).length < 2 ^ (prefixWord ++ tailWord_1808364).sum := by decide
  have hdescent : baseEnd_1808364 < baseStart_1808364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808391 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 8]
def baseStart_1808391 : Nat := 118140960795 + 1808391 * 2 ^ 59
def prefixEnd_1808391 : Nat := 4983230072969 + 3 ^ 40 * 1808391 * 2
def baseEnd_1808391 : Nat := 103174866029437710621763

theorem tailTrace_1808391 : CollatzResearch.WordTrace tailWord_1808391 prefixEnd_1808391 103174866029437710621763 := by
  unfold tailWord_1808391
  simp only [CollatzResearch.WordTrace]
  refine ⟨65957438391515730439217027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43971625594343820292811351 65957438391515730439217027)
  ·
    refine ⟨98936157587273595658825541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65957438391515730439217027 98936157587273595658825541)
    ·
      refine ⟨18550529547613799186029789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98936157587273595658825541 18550529547613799186029789)
      ·
        refine ⟨6956448580355174694761171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18550529547613799186029789 6956448580355174694761171)
        ·
          refine ⟨10434672870532762042141757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956448580355174694761171 10434672870532762042141757)
          ·
            refine ⟨3913002326449785765803159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10434672870532762042141757 3913002326449785765803159)
            ·
              refine ⟨5869503489674678648704739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913002326449785765803159 5869503489674678648704739)
              ·
                refine ⟨8804255234512017973057109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5869503489674678648704739 8804255234512017973057109)
                ·
                  refine ⟨103174866029437710621763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8804255234512017973057109 103174866029437710621763)
                  ·
                    rfl

theorem cell23_1808391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 8].length) (baseStart_1808391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808391 prefixEnd_1808391 := by exact prefixLift 1808391
  have htrace : WordTrace (prefixWord ++ tailWord_1808391) baseStart_1808391 baseEnd_1808391 := by
    simpa [prefixWord, tailWord_1808391, baseEnd_1808391] using wordTrace_append hprefix tailTrace_1808391
  have hstable : (prefixWord ++ tailWord_1808391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808391).length < 2 ^ (prefixWord ++ tailWord_1808391).sum := by decide
  have hdescent : baseEnd_1808391 < baseStart_1808391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808408 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 6]
def baseStart_1808408 : Nat := 118140960795 + 1808408 * 2 ^ 59
def prefixEnd_1808408 : Nat := 4983230072969 + 3 ^ 40 * 1808408 * 2
def baseEnd_1808408 : Nat := 103175835937340647675921

theorem tailTrace_1808408 : CollatzResearch.WordTrace tailWord_1808408 prefixEnd_1808408 103175835937340647675921 := by
  unfold tailWord_1808408
  simp only [CollatzResearch.WordTrace]
  refine ⟨32979029216227071171292939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43972038954969428228390585 32979029216227071171292939)
  ·
    refine ⟨49468543824340606756939409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32979029216227071171292939 49468543824340606756939409)
    ·
      refine ⟨37101407868255455067704557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49468543824340606756939409 37101407868255455067704557)
      ·
        refine ⟨13913027950595795650389209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37101407868255455067704557 13913027950595795650389209)
        ·
          refine ⟨10434770962946846737791907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13913027950595795650389209 10434770962946846737791907)
          ·
            refine ⟨15652156444420270106687861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10434770962946846737791907 15652156444420270106687861)
            ·
              refine ⟨1467389666664400322501987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15652156444420270106687861 1467389666664400322501987)
              ·
                refine ⟨2201084499996600483752981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467389666664400322501987 2201084499996600483752981)
                ·
                  refine ⟨103175835937340647675921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2201084499996600483752981 103175835937340647675921)
                  ·
                    rfl

theorem cell23_1808408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 6].length) (baseStart_1808408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808408 prefixEnd_1808408 := by exact prefixLift 1808408
  have htrace : WordTrace (prefixWord ++ tailWord_1808408) baseStart_1808408 baseEnd_1808408 := by
    simpa [prefixWord, tailWord_1808408, baseEnd_1808408] using wordTrace_append hprefix tailTrace_1808408
  have hstable : (prefixWord ++ tailWord_1808408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808408).length < 2 ^ (prefixWord ++ tailWord_1808408).sum := by decide
  have hdescent : baseEnd_1808408 < baseStart_1808408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808445 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_1808445 : Nat := 118140960795 + 1808445 * 2 ^ 59
def prefixEnd_1808445 : Nat := 4983230072969 + 3 ^ 40 * 1808445 * 2
def baseEnd_1808445 : Nat := 928601522220282184320619

theorem tailTrace_1808445 : CollatzResearch.WordTrace tailWord_1808445 prefixEnd_1808445 928601522220282184320619 := by
  unfold tailWord_1808445
  simp only [CollatzResearch.WordTrace]
  refine ⟨65959407933320097661682789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43972938622213398441121859 65959407933320097661682789)
  ·
    refine ⟨12367388987497518311565523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65959407933320097661682789 12367388987497518311565523)
    ·
      refine ⟨18551083481246277467348285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12367388987497518311565523 18551083481246277467348285)
      ·
        refine ⟨6956656305467354050255607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18551083481246277467348285 6956656305467354050255607)
        ·
          refine ⟨10434984458201031075383411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956656305467354050255607 10434984458201031075383411)
          ·
            refine ⟨15652476687301546613075117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10434984458201031075383411 15652476687301546613075117)
            ·
              refine ⟨5869678757738079979903169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15652476687301546613075117 5869678757738079979903169)
              ·
                refine ⟨4402259068303559984927377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5869678757738079979903169 4402259068303559984927377)
                ·
                  refine ⟨3301694301227669988695533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4402259068303559984927377 3301694301227669988695533)
                  ·
                    refine ⟨1238135362960376245760825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3301694301227669988695533 1238135362960376245760825)
                    ·
                      refine ⟨928601522220282184320619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1238135362960376245760825 928601522220282184320619)
                      ·
                        rfl

theorem cell23_1808445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_1808445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808445 prefixEnd_1808445 := by exact prefixLift 1808445
  have htrace : WordTrace (prefixWord ++ tailWord_1808445) baseStart_1808445 baseEnd_1808445 := by
    simpa [prefixWord, tailWord_1808445, baseEnd_1808445] using wordTrace_append hprefix tailTrace_1808445
  have hstable : (prefixWord ++ tailWord_1808445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808445).length < 2 ^ (prefixWord ++ tailWord_1808445).sum := by decide
  have hdescent : baseEnd_1808445 < baseStart_1808445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808471 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1808471 : Nat := 118140960795 + 1808471 * 2 ^ 59
def prefixEnd_1808471 : Nat := 4983230072969 + 3 ^ 40 * 1808471 * 2
def baseEnd_1808471 : Nat := 928614872717299082595499

theorem tailTrace_1808471 : CollatzResearch.WordTrace tailWord_1808471 prefixEnd_1808471 928614872717299082595499 := by
  unfold tailWord_1808471
  simp only [CollatzResearch.WordTrace]
  refine ⟨65960356231225904102129267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43973570820817269401419511 65960356231225904102129267)
  ·
    refine ⟨98940534346838856153193901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65960356231225904102129267 98940534346838856153193901)
    ·
      refine ⟨37102700380064571057447713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98940534346838856153193901 37102700380064571057447713)
      ·
        refine ⟨27827025285048428293085785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37102700380064571057447713 27827025285048428293085785)
        ·
          refine ⟨20870268963786321219814339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27827025285048428293085785 20870268963786321219814339)
          ·
            refine ⟨31305403445679481829721509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20870268963786321219814339 31305403445679481829721509)
            ·
              refine ⟨5869763146064902843072783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31305403445679481829721509 5869763146064902843072783)
              ·
                refine ⟨8804644719097354264609175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5869763146064902843072783 8804644719097354264609175)
                ·
                  refine ⟨13206967078646031396913763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8804644719097354264609175 13206967078646031396913763)
                  ·
                    refine ⟨19810450617969047095370645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13206967078646031396913763 19810450617969047095370645)
                    ·
                      refine ⟨928614872717299082595499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19810450617969047095370645 928614872717299082595499)
                      ·
                        rfl

theorem cell23_1808471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1808471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808471 prefixEnd_1808471 := by exact prefixLift 1808471
  have htrace : WordTrace (prefixWord ++ tailWord_1808471) baseStart_1808471 baseEnd_1808471 := by
    simpa [prefixWord, tailWord_1808471, baseEnd_1808471] using wordTrace_append hprefix tailTrace_1808471
  have hstable : (prefixWord ++ tailWord_1808471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808471).length < 2 ^ (prefixWord ++ tailWord_1808471).sum := by decide
  have hdescent : baseEnd_1808471 < baseStart_1808471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808502 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_1808502 : Nat := 118140960795 + 1808502 * 2 ^ 59
def prefixEnd_1808502 : Nat := 4983230072969 + 3 ^ 40 * 1808502 * 2
def baseEnd_1808502 : Nat := 309543596872529487102619

theorem tailTrace_1808502 : CollatzResearch.WordTrace tailWord_1808502 prefixEnd_1808502 309543596872529487102619 := by
  unfold tailWord_1808502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122592930882099774781735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43974324596075730931005173 4122592930882099774781735)
  ·
    refine ⟨6183889396323149662172603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4122592930882099774781735 6183889396323149662172603)
    ·
      refine ⟨9275834094484724493258905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6183889396323149662172603 9275834094484724493258905)
      ·
        refine ⟨6956875570863543369944179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9275834094484724493258905 6956875570863543369944179)
        ·
          refine ⟨10435313356295315054916269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6956875570863543369944179 10435313356295315054916269)
          ·
            refine ⟨3913242508610743145593601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10435313356295315054916269 3913242508610743145593601)
            ·
              refine ⟨2934931881458057359195201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3913242508610743145593601 2934931881458057359195201)
              ·
                refine ⟨2201198911093543019396401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2934931881458057359195201 2201198911093543019396401)
                ·
                  refine ⟨1650899183320157264547301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2201198911093543019396401 1650899183320157264547301)
                  ·
                    refine ⟨309543596872529487102619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1650899183320157264547301 309543596872529487102619)
                    ·
                      rfl

theorem cell23_1808502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_1808502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808502 prefixEnd_1808502 := by exact prefixLift 1808502
  have htrace : WordTrace (prefixWord ++ tailWord_1808502) baseStart_1808502 baseEnd_1808502 := by
    simpa [prefixWord, tailWord_1808502, baseEnd_1808502] using wordTrace_append hprefix tailTrace_1808502
  have hstable : (prefixWord ++ tailWord_1808502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808502).length < 2 ^ (prefixWord ++ tailWord_1808502).sum := by decide
  have hdescent : baseEnd_1808502 < baseStart_1808502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808509 : List Nat := [1, 4, 1, 1, 3, 3, 1, 4, 1, 2, 2]
def baseStart_1808509 : Nat := 118140960795 + 1808509 * 2 ^ 59
def prefixEnd_1808509 : Nat := 4983230072969 + 3 ^ 40 * 1808509 * 2
def baseEnd_1808509 : Nat := 928634384982169933920325

theorem tailTrace_1808509 : CollatzResearch.WordTrace tailWord_1808509 prefixEnd_1808509 928634384982169933920325 := by
  unfold tailWord_1808509
  simp only [CollatzResearch.WordTrace]
  refine ⟨65961742205088236592012581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43974494803392157728008387 65961742205088236592012581)
  ·
    refine ⟨12367826663454044361002359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65961742205088236592012581 12367826663454044361002359)
    ·
      refine ⟨18551739995181066541503539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12367826663454044361002359 18551739995181066541503539)
      ·
        refine ⟨27827609992771599812255309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18551739995181066541503539 27827609992771599812255309)
        ·
          refine ⟨10435353747289349929595741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27827609992771599812255309 10435353747289349929595741)
          ·
            refine ⟨3913257655233506223598403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10435353747289349929595741 3913257655233506223598403)
            ·
              refine ⟨5869886482850259335397605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913257655233506223598403 5869886482850259335397605)
              ·
                refine ⟨1100603715534423625387051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5869886482850259335397605 1100603715534423625387051)
                ·
                  refine ⟨1650905573301635438080577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100603715534423625387051 1650905573301635438080577)
                  ·
                    refine ⟨1238179179976226578560433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1650905573301635438080577 1238179179976226578560433)
                    ·
                      refine ⟨928634384982169933920325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1238179179976226578560433 928634384982169933920325)
                      ·
                        rfl

theorem cell23_1808509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_1808509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808509 prefixEnd_1808509 := by exact prefixLift 1808509
  have htrace : WordTrace (prefixWord ++ tailWord_1808509) baseStart_1808509 baseEnd_1808509 := by
    simpa [prefixWord, tailWord_1808509, baseEnd_1808509] using wordTrace_append hprefix tailTrace_1808509
  have hstable : (prefixWord ++ tailWord_1808509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808509).length < 2 ^ (prefixWord ++ tailWord_1808509).sum := by decide
  have hdescent : baseEnd_1808509 < baseStart_1808509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808531 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 4]
def baseStart_1808531 : Nat := 118140960795 + 1808531 * 2 ^ 59
def prefixEnd_1808531 : Nat := 4983230072969 + 3 ^ 40 * 1808531 * 2
def baseEnd_1808531 : Nat := 928645681556568847845223

theorem tailTrace_1808531 : CollatzResearch.WordTrace tailWord_1808531 prefixEnd_1808531 928645681556568847845223 := by
  unfold tailWord_1808531
  simp only [CollatzResearch.WordTrace]
  refine ⟨65962544611008534349313447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43975029740672356232875631 65962544611008534349313447)
  ·
    refine ⟨98943816916512801523970171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65962544611008534349313447 98943816916512801523970171)
    ·
      refine ⟨148415725374769202285955257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98943816916512801523970171 148415725374769202285955257)
      ·
        refine ⟨111311794031076901714466443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148415725374769202285955257 111311794031076901714466443)
        ·
          refine ⟨166967691046615352571699665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111311794031076901714466443 166967691046615352571699665)
          ·
            refine ⟨125225768284961514428774749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166967691046615352571699665 125225768284961514428774749)
            ·
              refine ⟨46959663106860567910790531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125225768284961514428774749 46959663106860567910790531)
              ·
                refine ⟨70439494660290851866185797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46959663106860567910790531 70439494660290851866185797)
                ·
                  refine ⟨13207405248804534724909837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70439494660290851866185797 13207405248804534724909837)
                  ·
                    refine ⟨4952776968301700521841189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13207405248804534724909837 4952776968301700521841189)
                    ·
                      refine ⟨928645681556568847845223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4952776968301700521841189 928645681556568847845223)
                      ·
                        rfl

theorem cell23_1808531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_1808531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808531 prefixEnd_1808531 := by exact prefixLift 1808531
  have htrace : WordTrace (prefixWord ++ tailWord_1808531) baseStart_1808531 baseEnd_1808531 := by
    simpa [prefixWord, tailWord_1808531, baseEnd_1808531] using wordTrace_append hprefix tailTrace_1808531
  have hstable : (prefixWord ++ tailWord_1808531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808531).length < 2 ^ (prefixWord ++ tailWord_1808531).sum := by decide
  have hdescent : baseEnd_1808531 < baseStart_1808531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808532 : List Nat := [2, 4, 2, 3, 1, 1, 3, 7]
def baseStart_1808532 : Nat := 118140960795 + 1808532 * 2 ^ 59
def prefixEnd_1808532 : Nat := 4983230072969 + 3 ^ 40 * 1808532 * 2
def baseEnd_1808532 : Nat := 34394303519897160886397

theorem tailTrace_1808532 : CollatzResearch.WordTrace tailWord_1808532 prefixEnd_1808532 34394303519897160886397 := by
  unfold tailWord_1808532
  simp only [CollatzResearch.WordTrace]
  refine ⟨32981290542002455760049925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43975054056003274346733233 32981290542002455760049925)
  ·
    refine ⟨6183991976625460455009361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32981290542002455760049925 6183991976625460455009361)
    ·
      refine ⟨4637993982469095341257021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6183991976625460455009361 4637993982469095341257021)
      ·
        refine ⟨1739247743425910752971383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4637993982469095341257021 1739247743425910752971383)
        ·
          refine ⟨2608871615138866129457075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739247743425910752971383 2608871615138866129457075)
          ·
            refine ⟨3913307422708299194185613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608871615138866129457075 3913307422708299194185613)
            ·
              refine ⟨1467490283515612197819605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3913307422708299194185613 1467490283515612197819605)
              ·
                refine ⟨34394303519897160886397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1467490283515612197819605 34394303519897160886397)
                ·
                  rfl

theorem cell23_1808532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 7].length) (baseStart_1808532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808532 prefixEnd_1808532 := by exact prefixLift 1808532
  have htrace : WordTrace (prefixWord ++ tailWord_1808532) baseStart_1808532 baseEnd_1808532 := by
    simpa [prefixWord, tailWord_1808532, baseEnd_1808532] using wordTrace_append hprefix tailTrace_1808532
  have hstable : (prefixWord ++ tailWord_1808532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808532).length < 2 ^ (prefixWord ++ tailWord_1808532).sum := by decide
  have hdescent : baseEnd_1808532 < baseStart_1808532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808668 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1808668 : Nat := 118140960795 + 1808668 * 2 ^ 59
def prefixEnd_1808668 : Nat := 4983230072969 + 3 ^ 40 * 1808668 * 2
def baseEnd_1808668 : Nat := 928716028406234811832093

theorem tailTrace_1808668 : CollatzResearch.WordTrace tailWord_1808668 prefixEnd_1808668 928716028406234811832093 := by
  unfold tailWord_1808668
  simp only [CollatzResearch.WordTrace]
  refine ⟨32983770705756103373525329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43978360941008137831367105 32983770705756103373525329)
  ·
    refine ⟨24737828029317077530143997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32983770705756103373525329 24737828029317077530143997)
    ·
      refine ⟨9276685510993904073803999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24737828029317077530143997 9276685510993904073803999)
      ·
        refine ⟨13915028266490856110705999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9276685510993904073803999 13915028266490856110705999)
        ·
          refine ⟨20872542399736284166058999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13915028266490856110705999 20872542399736284166058999)
          ·
            refine ⟨31308813599604426249088499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20872542399736284166058999 31308813599604426249088499)
            ·
              refine ⟨46963220399406639373632749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31308813599604426249088499 46963220399406639373632749)
              ·
                refine ⟨17611207649777489765112281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46963220399406639373632749 17611207649777489765112281)
                ·
                  refine ⟨13208405737333117323834211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17611207649777489765112281 13208405737333117323834211)
                  ·
                    refine ⟨19812608605999675985751317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13208405737333117323834211 19812608605999675985751317)
                    ·
                      refine ⟨928716028406234811832093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19812608605999675985751317 928716028406234811832093)
                      ·
                        rfl

theorem cell23_1808668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1808668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808668 prefixEnd_1808668 := by exact prefixLift 1808668
  have htrace : WordTrace (prefixWord ++ tailWord_1808668) baseStart_1808668 baseEnd_1808668 := by
    simpa [prefixWord, tailWord_1808668, baseEnd_1808668] using wordTrace_append hprefix tailTrace_1808668
  have hstable : (prefixWord ++ tailWord_1808668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808668).length < 2 ^ (prefixWord ++ tailWord_1808668).sum := by decide
  have hdescent : baseEnd_1808668 < baseStart_1808668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808675 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 3]
def baseStart_1808675 : Nat := 118140960795 + 1808675 * 2 ^ 59
def prefixEnd_1808675 : Nat := 4983230072969 + 3 ^ 40 * 1808675 * 2
def baseEnd_1808675 : Nat := 928719622770816284444561

theorem tailTrace_1808675 : CollatzResearch.WordTrace tailWord_1808675 prefixEnd_1808675 928719622770816284444561 := by
  unfold tailWord_1808675
  simp only [CollatzResearch.WordTrace]
  refine ⟨65967796722486846942555479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43978531148324564628370319 65967796722486846942555479)
  ·
    refine ⟨98951695083730270413833219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65967796722486846942555479 98951695083730270413833219)
    ·
      refine ⟨148427542625595405620749829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98951695083730270413833219 148427542625595405620749829)
      ·
        refine ⟨27830164242299138553890593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148427542625595405620749829 27830164242299138553890593)
        ·
          refine ⟨20872623181724353915417945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27830164242299138553890593 20872623181724353915417945)
          ·
            refine ⟨15654467386293265436563459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20872623181724353915417945 15654467386293265436563459)
            ·
              refine ⟨23481701079439898154845189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15654467386293265436563459 23481701079439898154845189)
              ·
                refine ⟨4402818952394980904033473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23481701079439898154845189 4402818952394980904033473)
                ·
                  refine ⟨3302114214296235678025105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4402818952394980904033473 3302114214296235678025105)
                  ·
                    refine ⟨2476585660722176758518829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3302114214296235678025105 2476585660722176758518829)
                    ·
                      refine ⟨928719622770816284444561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2476585660722176758518829 928719622770816284444561)
                      ·
                        rfl

theorem cell23_1808675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_1808675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808675 prefixEnd_1808675 := by exact prefixLift 1808675
  have htrace : WordTrace (prefixWord ++ tailWord_1808675) baseStart_1808675 baseEnd_1808675 := by
    simpa [prefixWord, tailWord_1808675, baseEnd_1808675] using wordTrace_append hprefix tailTrace_1808675
  have hstable : (prefixWord ++ tailWord_1808675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808675).length < 2 ^ (prefixWord ++ tailWord_1808675).sum := by decide
  have hdescent : baseEnd_1808675 < baseStart_1808675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808739 : List Nat := [1, 1, 1, 5, 2, 1, 1, 6, 1, 1, 3]
def baseStart_1808739 : Nat := 118140960795 + 1808739 * 2 ^ 59
def prefixEnd_1808739 : Nat := 4983230072969 + 3 ^ 40 * 1808739 * 2
def baseEnd_1808739 : Nat := 928752485532704034044267

theorem tailTrace_1808739 : CollatzResearch.WordTrace tailWord_1808739 prefixEnd_1808739 928752485532704034044267 := by
  unfold tailWord_1808739
  simp only [CollatzResearch.WordTrace]
  refine ⟨65970130994254985872885271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43980087329503323915256847 65970130994254985872885271)
  ·
    refine ⟨98955196491382478809327907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65970130994254985872885271 98955196491382478809327907)
    ·
      refine ⟨148432794737073718213991861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98955196491382478809327907 148432794737073718213991861)
      ·
        refine ⟨13915574506600661082561737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148432794737073718213991861 13915574506600661082561737)
        ·
          refine ⟨10436680879950495811921303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13915574506600661082561737 10436680879950495811921303)
          ·
            refine ⟨15655021319925743717881955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436680879950495811921303 15655021319925743717881955)
            ·
              refine ⟨23482531979888615576822933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15655021319925743717881955 23482531979888615576822933)
              ·
                refine ⟨1100743686557278855163575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23482531979888615576822933 1100743686557278855163575)
                ·
                  refine ⟨1651115529835918282745363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100743686557278855163575 1651115529835918282745363)
                  ·
                    refine ⟨2476673294753877424118045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1651115529835918282745363 2476673294753877424118045)
                    ·
                      refine ⟨928752485532704034044267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2476673294753877424118045 928752485532704034044267)
                      ·
                        rfl

theorem cell23_1808739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_1808739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808739 prefixEnd_1808739 := by exact prefixLift 1808739
  have htrace : WordTrace (prefixWord ++ tailWord_1808739) baseStart_1808739 baseEnd_1808739 := by
    simpa [prefixWord, tailWord_1808739, baseEnd_1808739] using wordTrace_append hprefix tailTrace_1808739
  have hstable : (prefixWord ++ tailWord_1808739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808739).length < 2 ^ (prefixWord ++ tailWord_1808739).sum := by decide
  have hdescent : baseEnd_1808739 < baseStart_1808739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808775 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1808775 : Nat := 118140960795 + 1808775 * 2 ^ 59
def prefixEnd_1808775 : Nat := 4983230072969 + 3 ^ 40 * 1808775 * 2
def baseEnd_1808775 : Nat := 928770970836265893194101

theorem tailTrace_1808775 : CollatzResearch.WordTrace tailWord_1808775 prefixEnd_1808775 928770970836265893194101 := by
  unfold tailWord_1808775
  simp only [CollatzResearch.WordTrace]
  refine ⟨65971444022124564021195779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43980962681416376014130519 65971444022124564021195779)
  ·
    refine ⟨98957166033186846031793669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65971444022124564021195779 98957166033186846031793669)
    ·
      refine ⟨18554468631222533630961313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98957166033186846031793669 18554468631222533630961313)
      ·
        refine ⟨13915851473416900223220985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18554468631222533630961313 13915851473416900223220985)
        ·
          refine ⟨10436888605062675167415739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13915851473416900223220985 10436888605062675167415739)
          ·
            refine ⟨15655332907594012751123609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436888605062675167415739 15655332907594012751123609)
            ·
              refine ⟨11741499680695509563342707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15655332907594012751123609 11741499680695509563342707)
              ·
                refine ⟨17612249521043264345014061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741499680695509563342707 17612249521043264345014061)
                ·
                  refine ⟨6604593570391224129380273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17612249521043264345014061 6604593570391224129380273)
                  ·
                    refine ⟨4953445177793418097035205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6604593570391224129380273 4953445177793418097035205)
                    ·
                      refine ⟨928770970836265893194101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4953445177793418097035205 928770970836265893194101)
                      ·
                        rfl

theorem cell23_1808775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1808775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808775 prefixEnd_1808775 := by exact prefixLift 1808775
  have htrace : WordTrace (prefixWord ++ tailWord_1808775) baseStart_1808775 baseEnd_1808775 := by
    simpa [prefixWord, tailWord_1808775, baseEnd_1808775] using wordTrace_append hprefix tailTrace_1808775
  have hstable : (prefixWord ++ tailWord_1808775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808775).length < 2 ^ (prefixWord ++ tailWord_1808775).sum := by decide
  have hdescent : baseEnd_1808775 < baseStart_1808775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808782 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1808782 : Nat := 118140960795 + 1808782 * 2 ^ 59
def prefixEnd_1808782 : Nat := 4983230072969 + 3 ^ 40 * 1808782 * 2
def baseEnd_1808782 : Nat := 928774565200847365806569

theorem tailTrace_1808782 : CollatzResearch.WordTrace tailWord_1808782 prefixEnd_1808782 928774565200847365806569 := by
  unfold tailWord_1808782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8246462416637400527087575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43981132888732802811133733 8246462416637400527087575)
  ·
    refine ⟨12369693624956100790631363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8246462416637400527087575 12369693624956100790631363)
    ·
      refine ⟨18554540437434151185947045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12369693624956100790631363 18554540437434151185947045)
      ·
        refine ⟨3478976332018903347365071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18554540437434151185947045 3478976332018903347365071)
        ·
          refine ⟨5218464498028355021047607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478976332018903347365071 5218464498028355021047607)
          ·
            refine ⟨7827696747042532531571411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218464498028355021047607 7827696747042532531571411)
            ·
              refine ⟨11741545120563798797357117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827696747042532531571411 11741545120563798797357117)
              ·
                refine ⟨4403079420211424549008919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11741545120563798797357117 4403079420211424549008919)
                ·
                  refine ⟨6604619130317136823513379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403079420211424549008919 6604619130317136823513379)
                  ·
                    refine ⟨9906928695475705235270069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6604619130317136823513379 9906928695475705235270069)
                    ·
                      refine ⟨928774565200847365806569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9906928695475705235270069 928774565200847365806569)
                      ·
                        rfl

theorem cell23_1808782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1808782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808782 prefixEnd_1808782 := by exact prefixLift 1808782
  have htrace : WordTrace (prefixWord ++ tailWord_1808782) baseStart_1808782 baseEnd_1808782 := by
    simpa [prefixWord, tailWord_1808782, baseEnd_1808782] using wordTrace_append hprefix tailTrace_1808782
  have hstable : (prefixWord ++ tailWord_1808782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808782).length < 2 ^ (prefixWord ++ tailWord_1808782).sum := by decide
  have hdescent : baseEnd_1808782 < baseStart_1808782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808810 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1808810 : Nat := 118140960795 + 1808810 * 2 ^ 59
def prefixEnd_1808810 : Nat := 4983230072969 + 3 ^ 40 * 1808810 * 2
def baseEnd_1808810 : Nat := 309596314219724418752147

theorem tailTrace_1808810 : CollatzResearch.WordTrace tailWord_1808810 prefixEnd_1808810 309596314219724418752147 := by
  unfold tailWord_1808810
  simp only [CollatzResearch.WordTrace]
  refine ⟨16493180144249441249679971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43981813717998509999146589 16493180144249441249679971)
  ·
    refine ⟨24739770216374161874519957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16493180144249441249679971 24739770216374161874519957)
    ·
      refine ⟨1159676728892538837868123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24739770216374161874519957 1159676728892538837868123)
      ·
        refine ⟨1739515093338808256802185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159676728892538837868123 1739515093338808256802185)
        ·
          refine ⟨1304636320004106192601639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1739515093338808256802185 1304636320004106192601639)
          ·
            refine ⟨1956954480006159288902459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304636320004106192601639 1956954480006159288902459)
            ·
              refine ⟨2935431720009238933353689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956954480006159288902459 2935431720009238933353689)
              ·
                refine ⟨2201573790006929200015267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935431720009238933353689 2201573790006929200015267)
                ·
                  refine ⟨3302360685010393800022901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201573790006929200015267 3302360685010393800022901)
                  ·
                    refine ⟨309596314219724418752147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3302360685010393800022901 309596314219724418752147)
                    ·
                      rfl

theorem cell23_1808810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1808810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808810 prefixEnd_1808810 := by exact prefixLift 1808810
  have htrace : WordTrace (prefixWord ++ tailWord_1808810) baseStart_1808810 baseEnd_1808810 := by
    simpa [prefixWord, tailWord_1808810, baseEnd_1808810] using wordTrace_append hprefix tailTrace_1808810
  have hstable : (prefixWord ++ tailWord_1808810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808810).length < 2 ^ (prefixWord ++ tailWord_1808810).sum := by decide
  have hdescent : baseEnd_1808810 < baseStart_1808810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808813 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_1808813 : Nat := 118140960795 + 1808813 * 2 ^ 59
def prefixEnd_1808813 : Nat := 4983230072969 + 3 ^ 40 * 1808813 * 2
def baseEnd_1808813 : Nat := 928790483101136744518927

theorem tailTrace_1808813 : CollatzResearch.WordTrace tailWord_1808813 prefixEnd_1808813 928790483101136744518927 := by
  unfold tailWord_1808813
  simp only [CollatzResearch.WordTrace]
  refine ⟨65972829995986896511079093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43981886663991264340719395 65972829995986896511079093)
  ·
    refine ⟨6184952812123771547913665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65972829995986896511079093 6184952812123771547913665)
    ·
      refine ⟨4638714609092828660935249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6184952812123771547913665 4638714609092828660935249)
      ·
        refine ⟨3479035956819621495701437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4638714609092828660935249 3479035956819621495701437)
        ·
          refine ⟨1304638483807358060888039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3479035956819621495701437 1304638483807358060888039)
          ·
            refine ⟨1956957725711037091332059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304638483807358060888039 1956957725711037091332059)
            ·
              refine ⟨2935436588566555636998089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956957725711037091332059 2935436588566555636998089)
              ·
                refine ⟨2201577441424916727748567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935436588566555636998089 2201577441424916727748567)
                ·
                  refine ⟨3302366162137375091622851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201577441424916727748567 3302366162137375091622851)
                  ·
                    refine ⟨4953549243206062637434277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3302366162137375091622851 4953549243206062637434277)
                    ·
                      refine ⟨928790483101136744518927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4953549243206062637434277 928790483101136744518927)
                      ·
                        rfl

theorem cell23_1808813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_1808813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808813 prefixEnd_1808813 := by exact prefixLift 1808813
  have htrace : WordTrace (prefixWord ++ tailWord_1808813) baseStart_1808813 baseEnd_1808813 := by
    simpa [prefixWord, tailWord_1808813, baseEnd_1808813] using wordTrace_append hprefix tailTrace_1808813
  have hstable : (prefixWord ++ tailWord_1808813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808813).length < 2 ^ (prefixWord ++ tailWord_1808813).sum := by decide
  have hdescent : baseEnd_1808813 < baseStart_1808813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808833 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1808833 : Nat := 118140960795 + 1808833 * 2 ^ 59
def prefixEnd_1808833 : Nat := 4983230072969 + 3 ^ 40 * 1808833 * 2
def baseEnd_1808833 : Nat := 928800752714226666268835

theorem tailTrace_1808833 : CollatzResearch.WordTrace tailWord_1808833 prefixEnd_1808833 928800752714226666268835 := by
  unfold tailWord_1808833
  simp only [CollatzResearch.WordTrace]
  refine ⟨65973559455914439926807153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43982372970609626617871435 65973559455914439926807153)
  ·
    refine ⟨49480169591935829945105365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65973559455914439926807153 49480169591935829945105365)
    ·
      refine ⟨1159691474810996014338407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 49480169591935829945105365 1159691474810996014338407)
      ·
        refine ⟨1739537212216494021507611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159691474810996014338407 1739537212216494021507611)
        ·
          refine ⟨2609305818324741032261417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739537212216494021507611 2609305818324741032261417)
          ·
            refine ⟨1956979363743555774196063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2609305818324741032261417 1956979363743555774196063)
            ·
              refine ⟨2935469045615333661294095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956979363743555774196063 2935469045615333661294095)
              ·
                refine ⟨4403203568423000491941143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935469045615333661294095 4403203568423000491941143)
                ·
                  refine ⟨6604805352634500737911715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403203568423000491941143 6604805352634500737911715)
                  ·
                    refine ⟨9907208028951751106867573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6604805352634500737911715 9907208028951751106867573)
                    ·
                      refine ⟨928800752714226666268835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9907208028951751106867573 928800752714226666268835)
                      ·
                        rfl

theorem cell23_1808833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1808833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808833 prefixEnd_1808833 := by exact prefixLift 1808833
  have htrace : WordTrace (prefixWord ++ tailWord_1808833) baseStart_1808833 baseEnd_1808833 := by
    simpa [prefixWord, tailWord_1808833, baseEnd_1808833] using wordTrace_append hprefix tailTrace_1808833
  have hstable : (prefixWord ++ tailWord_1808833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808833).length < 2 ^ (prefixWord ++ tailWord_1808833).sum := by decide
  have hdescent : baseEnd_1808833 < baseStart_1808833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808852 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1808852 : Nat := 118140960795 + 1808852 * 2 ^ 59
def prefixEnd_1808852 : Nat := 4983230072969 + 3 ^ 40 * 1808852 * 2
def baseEnd_1808852 : Nat := 928810508846662091931247

theorem tailTrace_1808852 : CollatzResearch.WordTrace tailWord_1808852 prefixEnd_1808852 928810508846662091931247 := by
  unfold tailWord_1808852
  simp only [CollatzResearch.WordTrace]
  refine ⟨32987126221422803085874405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43982834961897070781165873 32987126221422803085874405)
  ·
    refine ⟨6185086166516775578601451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32987126221422803085874405 6185086166516775578601451)
    ·
      refine ⟨9277629249775163367902177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6185086166516775578601451 9277629249775163367902177)
      ·
        refine ⟨6958221937331372525926633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9277629249775163367902177 6958221937331372525926633)
        ·
          refine ⟨5218666452998529394444975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6958221937331372525926633 5218666452998529394444975)
          ·
            refine ⟨7827999679497794091667463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218666452998529394444975 7827999679497794091667463)
            ·
              refine ⟨11741999519246691137501195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827999679497794091667463 11741999519246691137501195)
              ·
                refine ⟨17612999278870036706251793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741999519246691137501195 17612999278870036706251793)
                ·
                  refine ⟨13209749459152527529688845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17612999278870036706251793 13209749459152527529688845)
                  ·
                    refine ⟨4953656047182197823633317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13209749459152527529688845 4953656047182197823633317)
                    ·
                      refine ⟨928810508846662091931247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4953656047182197823633317 928810508846662091931247)
                      ·
                        rfl

theorem cell23_1808852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1808852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808852 prefixEnd_1808852 := by exact prefixLift 1808852
  have htrace : WordTrace (prefixWord ++ tailWord_1808852) baseStart_1808852 baseEnd_1808852 := by
    simpa [prefixWord, tailWord_1808852, baseEnd_1808852] using wordTrace_append hprefix tailTrace_1808852
  have hstable : (prefixWord ++ tailWord_1808852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808852).length < 2 ^ (prefixWord ++ tailWord_1808852).sum := by decide
  have hdescent : baseEnd_1808852 < baseStart_1808852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808875 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 7]
def baseStart_1808875 : Nat := 118140960795 + 1808875 * 2 ^ 59
def prefixEnd_1808875 : Nat := 4983230072969 + 3 ^ 40 * 1808875 * 2
def baseEnd_1808875 : Nat := 103202479877968389104849

theorem tailTrace_1808875 : CollatzResearch.WordTrace tailWord_1808875 prefixEnd_1808875 103202479877968389104849 := by
  unfold tailWord_1808875
  simp only [CollatzResearch.WordTrace]
  refine ⟨65975091321762281099836079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43983394214508187399890719 65975091321762281099836079)
  ·
    refine ⟨98962636982643421649754119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65975091321762281099836079 98962636982643421649754119)
    ·
      refine ⟨148443955473965132474631179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98962636982643421649754119 148443955473965132474631179)
      ·
        refine ⟨222665933210947698711946769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148443955473965132474631179 222665933210947698711946769)
        ·
          refine ⟨166999449908210774033960077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222665933210947698711946769 166999449908210774033960077)
          ·
            refine ⟨62624793715579040262735029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166999449908210774033960077 62624793715579040262735029)
            ·
              refine ⟨5871074410835535024631409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62624793715579040262735029 5871074410835535024631409)
              ·
                refine ⟨4403305808126651268473557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5871074410835535024631409 4403305808126651268473557)
                ·
                  refine ⟨103202479877968389104849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4403305808126651268473557 103202479877968389104849)
                  ·
                    rfl

theorem cell23_1808875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 7].length) (baseStart_1808875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808875 prefixEnd_1808875 := by exact prefixLift 1808875
  have htrace : WordTrace (prefixWord ++ tailWord_1808875) baseStart_1808875 baseEnd_1808875 := by
    simpa [prefixWord, tailWord_1808875, baseEnd_1808875] using wordTrace_append hprefix tailTrace_1808875
  have hstable : (prefixWord ++ tailWord_1808875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808875).length < 2 ^ (prefixWord ++ tailWord_1808875).sum := by decide
  have hdescent : baseEnd_1808875 < baseStart_1808875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808886 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_1808886 : Nat := 118140960795 + 1808886 * 2 ^ 59
def prefixEnd_1808886 : Nat := 4983230072969 + 3 ^ 40 * 1808886 * 2
def baseEnd_1808886 : Nat := 928827967188914958906091

theorem tailTrace_1808886 : CollatzResearch.WordTrace tailWord_1808886 prefixEnd_1808886 928827967188914958906091 := by
  unfold tailWord_1808886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123468282795151873655407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43983661683148286652324341 4123468282795151873655407)
  ·
    refine ⟨6185202424192727810483111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4123468282795151873655407 6185202424192727810483111)
    ·
      refine ⟨9277803636289091715724667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6185202424192727810483111 9277803636289091715724667)
      ·
        refine ⟨13916705454433637573587001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9277803636289091715724667 13916705454433637573587001)
        ·
          refine ⟨10437529090825228180190251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13916705454433637573587001 10437529090825228180190251)
          ·
            refine ⟨15656293636237842270285377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10437529090825228180190251 15656293636237842270285377)
            ·
              refine ⟨11742220227178381702714033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15656293636237842270285377 11742220227178381702714033)
              ·
                refine ⟨8806665170383786277035525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11742220227178381702714033 8806665170383786277035525)
                ·
                  refine ⟨1651249719446959926944161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8806665170383786277035525 1651249719446959926944161)
                  ·
                    refine ⟨1238437289585219945208121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1651249719446959926944161 1238437289585219945208121)
                    ·
                      refine ⟨928827967188914958906091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1238437289585219945208121 928827967188914958906091)
                      ·
                        rfl

theorem cell23_1808886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_1808886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808886 prefixEnd_1808886 := by exact prefixLift 1808886
  have htrace : WordTrace (prefixWord ++ tailWord_1808886) baseStart_1808886 baseEnd_1808886 := by
    simpa [prefixWord, tailWord_1808886, baseEnd_1808886] using wordTrace_append hprefix tailTrace_1808886
  have hstable : (prefixWord ++ tailWord_1808886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808886).length < 2 ^ (prefixWord ++ tailWord_1808886).sum := by decide
  have hdescent : baseEnd_1808886 < baseStart_1808886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808912 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 6, 5, 2]
def baseStart_1808912 : Nat := 118140960795 + 1808912 * 2 ^ 59
def prefixEnd_1808912 : Nat := 4983230072969 + 3 ^ 40 * 1808912 * 2
def baseEnd_1808912 : Nat := 928841317685931857180971

theorem tailTrace_1808912 : CollatzResearch.WordTrace tailWord_1808912 prefixEnd_1808912 928841317685931857180971 := by
  unfold tailWord_1808912
  simp only [CollatzResearch.WordTrace]
  refine ⟨32988220411314118209466495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43984293881752157612621993 32988220411314118209466495)
  ·
    refine ⟨49482330616971177314199743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32988220411314118209466495 49482330616971177314199743)
    ·
      refine ⟨74223495925456765971299615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49482330616971177314199743 74223495925456765971299615)
      ·
        refine ⟨111335243888185148956949423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74223495925456765971299615 111335243888185148956949423)
        ·
          refine ⟨167002865832277723435424135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111335243888185148956949423 167002865832277723435424135)
          ·
            refine ⟨250504298748416585153136203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167002865832277723435424135 250504298748416585153136203)
            ·
              refine ⟨375756448122624877729704305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250504298748416585153136203 375756448122624877729704305)
              ·
                refine ⟨281817336091968658297278229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375756448122624877729704305 281817336091968658297278229)
                ·
                  refine ⟨13210187629311030857684917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 281817336091968658297278229 13210187629311030857684917)
                  ·
                    refine ⟨1238455090247909142907961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13210187629311030857684917 1238455090247909142907961)
                    ·
                      refine ⟨928841317685931857180971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1238455090247909142907961 928841317685931857180971)
                      ·
                        rfl

theorem cell23_1808912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 5, 2].length) (baseStart_1808912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808912 prefixEnd_1808912 := by exact prefixLift 1808912
  have htrace : WordTrace (prefixWord ++ tailWord_1808912) baseStart_1808912 baseEnd_1808912 := by
    simpa [prefixWord, tailWord_1808912, baseEnd_1808912] using wordTrace_append hprefix tailTrace_1808912
  have hstable : (prefixWord ++ tailWord_1808912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808912).length < 2 ^ (prefixWord ++ tailWord_1808912).sum := by decide
  have hdescent : baseEnd_1808912 < baseStart_1808912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808915 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 7]
def baseStart_1808915 : Nat := 118140960795 + 1808915 * 2 ^ 59
def prefixEnd_1808915 : Nat := 4983230072969 + 3 ^ 40 * 1808915 * 2
def baseEnd_1808915 : Nat := 928842858127895345443457

theorem tailTrace_1808915 : CollatzResearch.WordTrace tailWord_1808915 prefixEnd_1808915 928842858127895345443457 := by
  unfold tailWord_1808915
  simp only [CollatzResearch.WordTrace]
  refine ⟨65976550241617367931292199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43984366827744911954194799 65976550241617367931292199)
  ·
    refine ⟨98964825362426051896938299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65976550241617367931292199 98964825362426051896938299)
    ·
      refine ⟨148447238043639077845407449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98964825362426051896938299 148447238043639077845407449)
      ·
        refine ⟨111335428532729308384055587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148447238043639077845407449 111335428532729308384055587)
        ·
          refine ⟨167003142799093962576083381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111335428532729308384055587 167003142799093962576083381)
          ·
            refine ⟨15656544637415058991507817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167003142799093962576083381 15656544637415058991507817)
            ·
              refine ⟨11742408478061294243630863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15656544637415058991507817 11742408478061294243630863)
              ·
                refine ⟨17613612717091941365446295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11742408478061294243630863 17613612717091941365446295)
                ·
                  refine ⟨26420419075637912048169443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17613612717091941365446295 26420419075637912048169443)
                  ·
                    refine ⟨39630628613456868072254165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26420419075637912048169443 39630628613456868072254165)
                    ·
                      refine ⟨928842858127895345443457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39630628613456868072254165 928842858127895345443457)
                      ·
                        rfl

theorem cell23_1808915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_1808915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808915 prefixEnd_1808915 := by exact prefixLift 1808915
  have htrace : WordTrace (prefixWord ++ tailWord_1808915) baseStart_1808915 baseEnd_1808915 := by
    simpa [prefixWord, tailWord_1808915, baseEnd_1808915] using wordTrace_append hprefix tailTrace_1808915
  have hstable : (prefixWord ++ tailWord_1808915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808915).length < 2 ^ (prefixWord ++ tailWord_1808915).sum := by decide
  have hdescent : baseEnd_1808915 < baseStart_1808915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808955 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 6]
def baseStart_1808955 : Nat := 118140960795 + 1808955 * 2 ^ 59
def prefixEnd_1808955 : Nat := 4983230072969 + 3 ^ 40 * 1808955 * 2
def baseEnd_1808955 : Nat := 928863397354075188943273

theorem tailTrace_1808955 : CollatzResearch.WordTrace tailWord_1808955 prefixEnd_1808955 928863397354075188943273 := by
  unfold tailWord_1808955
  simp only [CollatzResearch.WordTrace]
  refine ⟨65978009161472454762748319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43985339440981636508498879 65978009161472454762748319)
  ·
    refine ⟨98967013742208682144122479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65978009161472454762748319 98967013742208682144122479)
    ·
      refine ⟨148450520613313023216183719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98967013742208682144122479 148450520613313023216183719)
      ·
        refine ⟨222675780919969534824275579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148450520613313023216183719 222675780919969534824275579)
        ·
          refine ⟨334013671379954302236413369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222675780919969534824275579 334013671379954302236413369)
          ·
            refine ⟨250510253534965726677310027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334013671379954302236413369 250510253534965726677310027)
            ·
              refine ⟨375765380302448590015965041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250510253534965726677310027 375765380302448590015965041)
              ·
                refine ⟨281824035226836442511973781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375765380302448590015965041 281824035226836442511973781)
                ·
                  refine ⟨13210501651257958242748771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 281824035226836442511973781 13210501651257958242748771)
                  ·
                    refine ⟨19815752476886937364123157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13210501651257958242748771 19815752476886937364123157)
                    ·
                      refine ⟨928863397354075188943273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19815752476886937364123157 928863397354075188943273)
                      ·
                        rfl

theorem cell23_1808955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_1808955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808955 prefixEnd_1808955 := by exact prefixLift 1808955
  have htrace : WordTrace (prefixWord ++ tailWord_1808955) baseStart_1808955 baseEnd_1808955 := by
    simpa [prefixWord, tailWord_1808955, baseEnd_1808955] using wordTrace_append hprefix tailTrace_1808955
  have hstable : (prefixWord ++ tailWord_1808955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808955).length < 2 ^ (prefixWord ++ tailWord_1808955).sum := by decide
  have hdescent : baseEnd_1808955 < baseStart_1808955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808966 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1808966 : Nat := 118140960795 + 1808966 * 2 ^ 59
def prefixEnd_1808966 : Nat := 4983230072969 + 3 ^ 40 * 1808966 * 2
def baseEnd_1808966 : Nat := 928869045641274645905723

theorem tailTrace_1808966 : CollatzResearch.WordTrace tailWord_1808966 prefixEnd_1808966 928869045641274645905723 := by
  unfold tailWord_1808966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061825323888518863793711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43985606909621735760932501 2061825323888518863793711)
  ·
    refine ⟨3092737985832778295690567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2061825323888518863793711 3092737985832778295690567)
    ·
      refine ⟨4639106978749167443535851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092737985832778295690567 4639106978749167443535851)
      ·
        refine ⟨6958660468123751165303777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639106978749167443535851 6958660468123751165303777)
        ·
          refine ⟨5218995351092813373977833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6958660468123751165303777 5218995351092813373977833)
          ·
            refine ⟨3914246513319610030483375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5218995351092813373977833 3914246513319610030483375)
            ·
              refine ⟨5871369769979415045725063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914246513319610030483375 5871369769979415045725063)
              ·
                refine ⟨8807054654969122568587595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871369769979415045725063 8807054654969122568587595)
                ·
                  refine ⟨13210581982453683852881393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8807054654969122568587595 13210581982453683852881393)
                  ·
                    refine ⟨9907936486840262889661045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13210581982453683852881393 9907936486840262889661045)
                    ·
                      refine ⟨928869045641274645905723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9907936486840262889661045 928869045641274645905723)
                      ·
                        rfl

theorem cell23_1808966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1808966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808966 prefixEnd_1808966 := by exact prefixLift 1808966
  have htrace : WordTrace (prefixWord ++ tailWord_1808966) baseStart_1808966 baseEnd_1808966 := by
    simpa [prefixWord, tailWord_1808966, baseEnd_1808966] using wordTrace_append hprefix tailTrace_1808966
  have hstable : (prefixWord ++ tailWord_1808966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808966).length < 2 ^ (prefixWord ++ tailWord_1808966).sum := by decide
  have hdescent : baseEnd_1808966 < baseStart_1808966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808990 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1808990 : Nat := 118140960795 + 1808990 * 2 ^ 59
def prefixEnd_1808990 : Nat := 4983230072969 + 3 ^ 40 * 1808990 * 2
def baseEnd_1808990 : Nat := 309627123058994184001871

theorem tailTrace_1808990 : CollatzResearch.WordTrace tailWord_1808990 prefixEnd_1808990 309627123058994184001871 := by
  unfold tailWord_1808990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8247410714543206967534053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43986190477563770493514949 8247410714543206967534053)
  ·
    refine ⟨1546389508976851306412635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8247410714543206967534053 1546389508976851306412635)
    ·
      refine ⟨2319584263465276959618953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1546389508976851306412635 2319584263465276959618953)
      ·
        refine ⟨1739688197598957719714215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2319584263465276959618953 1739688197598957719714215)
        ·
          refine ⟨2609532296398436579571323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739688197598957719714215 2609532296398436579571323)
          ·
            refine ⟨3914298444597654869356985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609532296398436579571323 3914298444597654869356985)
            ·
              refine ⟨2935723833448241152017739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3914298444597654869356985 2935723833448241152017739)
              ·
                refine ⟨4403585750172361728026609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935723833448241152017739 4403585750172361728026609)
                ·
                  refine ⟨3302689312629271296019957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4403585750172361728026609 3302689312629271296019957)
                  ·
                    refine ⟨309627123058994184001871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3302689312629271296019957 309627123058994184001871)
                    ·
                      rfl

theorem cell23_1808990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1808990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808990 prefixEnd_1808990 := by exact prefixLift 1808990
  have htrace : WordTrace (prefixWord ++ tailWord_1808990) baseStart_1808990 baseEnd_1808990 := by
    simpa [prefixWord, tailWord_1808990, baseEnd_1808990] using wordTrace_append hprefix tailTrace_1808990
  have hstable : (prefixWord ++ tailWord_1808990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808990).length < 2 ^ (prefixWord ++ tailWord_1808990).sum := by decide
  have hdescent : baseEnd_1808990 < baseStart_1808990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1808992 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 3]
def baseStart_1808992 : Nat := 118140960795 + 1808992 * 2 ^ 59
def prefixEnd_1808992 : Nat := 4983230072969 + 3 ^ 40 * 1808992 * 2
def baseEnd_1808992 : Nat := 928882396138291544180603

theorem tailTrace_1808992 : CollatzResearch.WordTrace tailWord_1808992 prefixEnd_1808992 928882396138291544180603 := by
  unfold tailWord_1808992
  simp only [CollatzResearch.WordTrace]
  refine ⟨32989679331169205040922615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43986239108225606721230153 32989679331169205040922615)
  ·
    refine ⟨49484518996753807561383923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32989679331169205040922615 49484518996753807561383923)
    ·
      refine ⟨74226778495130711342075885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49484518996753807561383923 74226778495130711342075885)
      ·
        refine ⟨27835041935674016753278457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74226778495130711342075885 27835041935674016753278457)
        ·
          refine ⟨20876281451755512564958843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27835041935674016753278457 20876281451755512564958843)
          ·
            refine ⟨31314422177633268847438265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20876281451755512564958843 31314422177633268847438265)
            ·
              refine ⟨23485816633224951635578699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31314422177633268847438265 23485816633224951635578699)
              ·
                refine ⟨35228724949837427453368049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23485816633224951635578699 35228724949837427453368049)
                ·
                  refine ⟨26421543712378070590026037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35228724949837427453368049 26421543712378070590026037)
                  ·
                    refine ⟨2477019723035444117814941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26421543712378070590026037 2477019723035444117814941)
                    ·
                      refine ⟨928882396138291544180603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2477019723035444117814941 928882396138291544180603)
                      ·
                        rfl

theorem cell23_1808992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_1808992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1808992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1808992 prefixEnd_1808992 := by exact prefixLift 1808992
  have htrace : WordTrace (prefixWord ++ tailWord_1808992) baseStart_1808992 baseEnd_1808992 := by
    simpa [prefixWord, tailWord_1808992, baseEnd_1808992] using wordTrace_append hprefix tailTrace_1808992
  have hstable : (prefixWord ++ tailWord_1808992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1808992).length < 2 ^ (prefixWord ++ tailWord_1808992).sum := by decide
  have hdescent : baseEnd_1808992 < baseStart_1808992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1808992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809019 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 4, 3, 2]
def baseStart_1809019 : Nat := 118140960795 + 1809019 * 2 ^ 59
def prefixEnd_1809019 : Nat := 4983230072969 + 3 ^ 40 * 1809019 * 2
def baseEnd_1809019 : Nat := 928896260115962938542979

theorem tailTrace_1809019 : CollatzResearch.WordTrace tailWord_1809019 prefixEnd_1809019 928896260115962938542979 := by
  unfold tailWord_1809019
  simp only [CollatzResearch.WordTrace]
  refine ⟨65980343433240593693078111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43986895622160395795385407 65980343433240593693078111)
  ·
    refine ⟨98970515149860890539617167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65980343433240593693078111 98970515149860890539617167)
    ·
      refine ⟨148455772724791335809425751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98970515149860890539617167 148455772724791335809425751)
      ·
        refine ⟨222683659087187003714138627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148455772724791335809425751 222683659087187003714138627)
        ·
          refine ⟨334025488630780505571207941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222683659087187003714138627 334025488630780505571207941)
          ·
            refine ⟨62629779118271344794601489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334025488630780505571207941 62629779118271344794601489)
            ·
              refine ⟨46972334338703508595951117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62629779118271344794601489 46972334338703508595951117)
              ·
                refine ⟨17614625377013815723481669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46972334338703508595951117 17614625377013815723481669)
                ·
                  refine ⟨3302742258190090448152813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17614625377013815723481669 3302742258190090448152813)
                  ·
                    refine ⟨1238528346821283918057305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302742258190090448152813 1238528346821283918057305)
                    ·
                      refine ⟨928896260115962938542979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1238528346821283918057305 928896260115962938542979)
                      ·
                        rfl

theorem cell23_1809019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 3, 2].length) (baseStart_1809019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809019 prefixEnd_1809019 := by exact prefixLift 1809019
  have htrace : WordTrace (prefixWord ++ tailWord_1809019) baseStart_1809019 baseEnd_1809019 := by
    simpa [prefixWord, tailWord_1809019, baseEnd_1809019] using wordTrace_append hprefix tailTrace_1809019
  have hstable : (prefixWord ++ tailWord_1809019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809019).length < 2 ^ (prefixWord ++ tailWord_1809019).sum := by decide
  have hdescent : baseEnd_1809019 < baseStart_1809019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809049 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 4]
def baseStart_1809049 : Nat := 118140960795 + 1809049 * 2 ^ 59
def prefixEnd_1809049 : Nat := 4983230072969 + 3 ^ 40 * 1809049 * 2
def baseEnd_1809049 : Nat := 928911664535597821167841

theorem tailTrace_1809049 : CollatzResearch.WordTrace tailWord_1809049 prefixEnd_1809049 928911664535597821167841 := by
  unfold tailWord_1809049
  simp only [CollatzResearch.WordTrace]
  refine ⟨65981437623131908816670201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43987625082087939211113467 65981437623131908816670201)
  ·
    refine ⟨49486078217348931612502651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65981437623131908816670201 49486078217348931612502651)
    ·
      refine ⟨74229117326023397418753977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49486078217348931612502651 74229117326023397418753977)
      ·
        refine ⟨55671837994517548064065483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74229117326023397418753977 55671837994517548064065483)
        ·
          refine ⟨83507756991776322096098225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55671837994517548064065483 83507756991776322096098225)
          ·
            refine ⟨62630817743832241572073669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83507756991776322096098225 62630817743832241572073669)
            ·
              refine ⟨11743278326968545294763813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62630817743832241572073669 11743278326968545294763813)
              ·
                refine ⟨2201864686306602242768215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11743278326968545294763813 2201864686306602242768215)
                ·
                  refine ⟨3302797029459903364152323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201864686306602242768215 3302797029459903364152323)
                  ·
                    refine ⟨4954195544189855046228485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3302797029459903364152323 4954195544189855046228485)
                    ·
                      refine ⟨928911664535597821167841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4954195544189855046228485 928911664535597821167841)
                      ·
                        rfl

theorem cell23_1809049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_1809049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809049 prefixEnd_1809049 := by exact prefixLift 1809049
  have htrace : WordTrace (prefixWord ++ tailWord_1809049) baseStart_1809049 baseEnd_1809049 := by
    simpa [prefixWord, tailWord_1809049, baseEnd_1809049] using wordTrace_append hprefix tailTrace_1809049
  have hstable : (prefixWord ++ tailWord_1809049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809049).length < 2 ^ (prefixWord ++ tailWord_1809049).sum := by decide
  have hdescent : baseEnd_1809049 < baseStart_1809049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809063 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1809063 : Nat := 118140960795 + 1809063 * 2 ^ 59
def prefixEnd_1809063 : Nat := 4983230072969 + 3 ^ 40 * 1809063 * 2
def baseEnd_1809063 : Nat := 309639617754920255464259

theorem tailTrace_1809063 : CollatzResearch.WordTrace tailWord_1809063 prefixEnd_1809063 309639617754920255464259 := by
  unfold tailWord_1809063
  simp only [CollatzResearch.WordTrace]
  refine ⟨65981948245081189207679843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43987965496720792805119895 65981948245081189207679843)
  ·
    refine ⟨98972922367621783811519765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65981948245081189207679843 98972922367621783811519765)
    ·
      refine ⟨4639355735982271116164989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98972922367621783811519765 4639355735982271116164989)
      ·
        refine ⟨1739758400993351668561871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4639355735982271116164989 1739758400993351668561871)
        ·
          refine ⟨2609637601490027502842807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739758400993351668561871 2609637601490027502842807)
          ·
            refine ⟨3914456402235041254264211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609637601490027502842807 3914456402235041254264211)
            ·
              refine ⟨5871684603352561881396317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914456402235041254264211 5871684603352561881396317)
              ·
                refine ⟨2201881726257210705523619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5871684603352561881396317 2201881726257210705523619)
                ·
                  refine ⟨3302822589385816058285429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201881726257210705523619 3302822589385816058285429)
                  ·
                    refine ⟨309639617754920255464259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3302822589385816058285429 309639617754920255464259)
                    ·
                      rfl

theorem cell23_1809063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1809063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809063 prefixEnd_1809063 := by exact prefixLift 1809063
  have htrace : WordTrace (prefixWord ++ tailWord_1809063) baseStart_1809063 baseEnd_1809063 := by
    simpa [prefixWord, tailWord_1809063, baseEnd_1809063] using wordTrace_append hprefix tailTrace_1809063
  have hstable : (prefixWord ++ tailWord_1809063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809063).length < 2 ^ (prefixWord ++ tailWord_1809063).sum := by decide
  have hdescent : baseEnd_1809063 < baseStart_1809063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809096 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_1809096 : Nat := 118140960795 + 1809096 * 2 ^ 59
def prefixEnd_1809096 : Nat := 4983230072969 + 3 ^ 40 * 1809096 * 2
def baseEnd_1809096 : Nat := 928935798126359137280125

theorem tailTrace_1809096 : CollatzResearch.WordTrace tailWord_1809096 prefixEnd_1809096 928935798126359137280125 := by
  unfold tailWord_1809096
  simp only [CollatzResearch.WordTrace]
  refine ⟨32991575926980817921815571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43988767902641090562420761 32991575926980817921815571)
  ·
    refine ⟨49487363890471226882723357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32991575926980817921815571 49487363890471226882723357)
    ·
      refine ⟨18557761458926710081021259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49487363890471226882723357 18557761458926710081021259)
      ·
        refine ⟨27836642188390065121531889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18557761458926710081021259 27836642188390065121531889)
        ·
          refine ⟨20877481641292548841148917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27836642188390065121531889 20877481641292548841148917)
          ·
            refine ⟨1957263903871176453857711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20877481641292548841148917 1957263903871176453857711)
            ·
              refine ⟨2935895855806764680786567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957263903871176453857711 2935895855806764680786567)
              ·
                refine ⟨4403843783710147021179851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935895855806764680786567 4403843783710147021179851)
                ·
                  refine ⟨6605765675565220531769777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403843783710147021179851 6605765675565220531769777)
                  ·
                    refine ⟨4954324256673915398827333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6605765675565220531769777 4954324256673915398827333)
                    ·
                      refine ⟨928935798126359137280125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4954324256673915398827333 928935798126359137280125)
                      ·
                        rfl

theorem cell23_1809096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_1809096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809096 prefixEnd_1809096 := by exact prefixLift 1809096
  have htrace : WordTrace (prefixWord ++ tailWord_1809096) baseStart_1809096 baseEnd_1809096 := by
    simpa [prefixWord, tailWord_1809096, baseEnd_1809096] using wordTrace_append hprefix tailTrace_1809096
  have hstable : (prefixWord ++ tailWord_1809096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809096).length < 2 ^ (prefixWord ++ tailWord_1809096).sum := by decide
  have hdescent : baseEnd_1809096 < baseStart_1809096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809133 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1809133 : Nat := 118140960795 + 1809133 * 2 ^ 59
def prefixEnd_1809133 : Nat := 4983230072969 + 3 ^ 40 * 1809133 * 2
def baseEnd_1809133 : Nat := 928954796910575492517455

theorem tailTrace_1809133 : CollatzResearch.WordTrace tailWord_1809133 prefixEnd_1809133 928954796910575492517455 := by
  unfold tailWord_1809133
  simp only [CollatzResearch.WordTrace]
  refine ⟨65984501354827591162728053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43989667569885060775152035 65984501354827591162728053)
  ·
    refine ⟨6186047002015086671505755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65984501354827591162728053 6186047002015086671505755)
    ·
      refine ⟨9279070503022630007258633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6186047002015086671505755 9279070503022630007258633)
      ·
        refine ⟨6959302877266972505443975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9279070503022630007258633 6959302877266972505443975)
        ·
          refine ⟨10438954315900458758165963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959302877266972505443975 10438954315900458758165963)
          ·
            refine ⟨15658431473850688137248945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10438954315900458758165963 15658431473850688137248945)
            ·
              refine ⟨11743823605388016102936709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15658431473850688137248945 11743823605388016102936709)
              ·
                refine ⟨2201966926010253019300633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11743823605388016102936709 2201966926010253019300633)
                ·
                  refine ⟨1651475194507689764475475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2201966926010253019300633 1651475194507689764475475)
                  ·
                    refine ⟨2477212791761534646713213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1651475194507689764475475 2477212791761534646713213)
                    ·
                      refine ⟨928954796910575492517455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2477212791761534646713213 928954796910575492517455)
                      ·
                        rfl

theorem cell23_1809133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1809133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809133 prefixEnd_1809133 := by exact prefixLift 1809133
  have htrace : WordTrace (prefixWord ++ tailWord_1809133) baseStart_1809133 baseEnd_1809133 := by
    simpa [prefixWord, tailWord_1809133, baseEnd_1809133] using wordTrace_append hprefix tailTrace_1809133
  have hstable : (prefixWord ++ tailWord_1809133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809133).length < 2 ^ (prefixWord ++ tailWord_1809133).sum := by decide
  have hdescent : baseEnd_1809133 < baseStart_1809133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809150 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1809150 : Nat := 118140960795 + 1809150 * 2 ^ 59
def prefixEnd_1809150 : Nat := 4983230072969 + 3 ^ 40 * 1809150 * 2
def baseEnd_1809150 : Nat := 928963526081701926004877

theorem tailTrace_1809150 : CollatzResearch.WordTrace tailWord_1809150 prefixEnd_1809150 928963526081701926004877 := by
  unfold tailWord_1809150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8248140174470750383262113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43990080930510668710731269 8248140174470750383262113)
  ·
    refine ⟨6186105130853062787446585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8248140174470750383262113 6186105130853062787446585)
    ·
      refine ⟨4639578848139797090584939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6186105130853062787446585 4639578848139797090584939)
      ·
        refine ⟨6959368272209695635877409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639578848139797090584939 6959368272209695635877409)
        ·
          refine ⟨5219526204157271726908057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6959368272209695635877409 5219526204157271726908057)
          ·
            refine ⟨3914644653117953795181043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5219526204157271726908057 3914644653117953795181043)
            ·
              refine ⟨5871966979676930692771565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914644653117953795181043 5871966979676930692771565)
              ·
                refine ⟨2201987617378849009789337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5871966979676930692771565 2201987617378849009789337)
                ·
                  refine ⟨1651490713034136757342003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2201987617378849009789337 1651490713034136757342003)
                  ·
                    refine ⟨2477236069551205136013005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1651490713034136757342003 2477236069551205136013005)
                    ·
                      refine ⟨928963526081701926004877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2477236069551205136013005 928963526081701926004877)
                      ·
                        rfl

theorem cell23_1809150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1809150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809150 prefixEnd_1809150 := by exact prefixLift 1809150
  have htrace : WordTrace (prefixWord ++ tailWord_1809150) baseStart_1809150 baseEnd_1809150 := by
    simpa [prefixWord, tailWord_1809150, baseEnd_1809150] using wordTrace_append hprefix tailTrace_1809150
  have hstable : (prefixWord ++ tailWord_1809150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809150).length < 2 ^ (prefixWord ++ tailWord_1809150).sum := by decide
  have hdescent : baseEnd_1809150 < baseStart_1809150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809160 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_1809160 : Nat := 118140960795 + 1809160 * 2 ^ 59
def prefixEnd_1809160 : Nat := 4983230072969 + 3 ^ 40 * 1809160 * 2
def baseEnd_1809160 : Nat := 928968660888246886879831

theorem tailTrace_1809160 : CollatzResearch.WordTrace tailWord_1809160 prefixEnd_1809160 928968660888246886879831 := by
  unfold tailWord_1809160
  simp only [CollatzResearch.WordTrace]
  refine ⟨32992743062864887386980467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43990324083819849849307289 32992743062864887386980467)
  ·
    refine ⟨49489114594297331080470701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32992743062864887386980467 49489114594297331080470701)
    ·
      refine ⟨18558417972861499155176513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49489114594297331080470701 18558417972861499155176513)
      ·
        refine ⟨13918813479646124366382385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18558417972861499155176513 13918813479646124366382385)
        ·
          refine ⟨10439110109734593274786789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13918813479646124366382385 10439110109734593274786789)
          ·
            refine ⟨1957333145575236239022523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10439110109734593274786789 1957333145575236239022523)
            ·
              refine ⟨2935999718362854358533785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957333145575236239022523 2935999718362854358533785)
              ·
                refine ⟨2201999788772140768900339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935999718362854358533785 2201999788772140768900339)
                ·
                  refine ⟨3302999683158211153350509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201999788772140768900339 3302999683158211153350509)
                  ·
                    refine ⟨1238624881184329182506441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302999683158211153350509 1238624881184329182506441)
                    ·
                      refine ⟨928968660888246886879831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1238624881184329182506441 928968660888246886879831)
                      ·
                        rfl

theorem cell23_1809160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_1809160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809160 prefixEnd_1809160 := by exact prefixLift 1809160
  have htrace : WordTrace (prefixWord ++ tailWord_1809160) baseStart_1809160 baseEnd_1809160 := by
    simpa [prefixWord, tailWord_1809160, baseEnd_1809160] using wordTrace_append hprefix tailTrace_1809160
  have hstable : (prefixWord ++ tailWord_1809160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809160).length < 2 ^ (prefixWord ++ tailWord_1809160).sum := by decide
  have hdescent : baseEnd_1809160 < baseStart_1809160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809196 : List Nat := [2, 2, 1, 1, 1, 4, 3, 4, 5]
def baseStart_1809196 : Nat := 118140960795 + 1809196 * 2 ^ 59
def prefixEnd_1809196 : Nat := 4983230072969 + 3 ^ 40 * 1809196 * 2
def baseEnd_1809196 : Nat := 103220794021312082892185

theorem tailTrace_1809196 : CollatzResearch.WordTrace tailWord_1809196 prefixEnd_1809196 103220794021312082892185 := by
  unfold tailWord_1809196
  simp only [CollatzResearch.WordTrace]
  refine ⟨32993399576799676461135721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43991199435732901948180961 32993399576799676461135721)
  ·
    refine ⟨24745049682599757345851791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32993399576799676461135721 24745049682599757345851791)
    ·
      refine ⟨37117574523899636018777687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24745049682599757345851791 37117574523899636018777687)
      ·
        refine ⟨55676361785849454028166531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37117574523899636018777687 55676361785849454028166531)
        ·
          refine ⟨83514542678774181042249797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55676361785849454028166531 83514542678774181042249797)
          ·
            refine ⟨15658976752270158945421837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83514542678774181042249797 15658976752270158945421837)
            ·
              refine ⟨5872116282101309604533189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15658976752270158945421837 5872116282101309604533189)
              ·
                refine ⟨1101021802893995550849973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5872116282101309604533189 1101021802893995550849973)
                ·
                  refine ⟨103220794021312082892185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1101021802893995550849973 103220794021312082892185)
                  ·
                    rfl

theorem cell23_1809196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_1809196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809196 prefixEnd_1809196 := by exact prefixLift 1809196
  have htrace : WordTrace (prefixWord ++ tailWord_1809196) baseStart_1809196 baseEnd_1809196 := by
    simpa [prefixWord, tailWord_1809196, baseEnd_1809196] using wordTrace_append hprefix tailTrace_1809196
  have hstable : (prefixWord ++ tailWord_1809196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809196).length < 2 ^ (prefixWord ++ tailWord_1809196).sum := by decide
  have hdescent : baseEnd_1809196 < baseStart_1809196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809266 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1809266 : Nat := 118140960795 + 1809266 * 2 ^ 59
def prefixEnd_1809266 : Nat := 4983230072969 + 3 ^ 40 * 1809266 * 2
def baseEnd_1809266 : Nat := 929023089837623472154343

theorem tailTrace_1809266 : CollatzResearch.WordTrace tailWord_1809266 prefixEnd_1809266 929023089837623472154343 := by
  unfold tailWord_1809266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16497338065836438719329913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43992901508897169918213101 16497338065836438719329913)
  ·
    refine ⟨12373003549377329039497435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16497338065836438719329913 12373003549377329039497435)
    ·
      refine ⟨18559505324065993559246153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12373003549377329039497435 18559505324065993559246153)
      ·
        refine ⟨13919628993049495169434615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18559505324065993559246153 13919628993049495169434615)
        ·
          refine ⟨20879443489574242754151923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13919628993049495169434615 20879443489574242754151923)
          ·
            refine ⟨31319165234361364131227885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20879443489574242754151923 31319165234361364131227885)
            ·
              refine ⟨11744686962885511549210457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31319165234361364131227885 11744686962885511549210457)
              ·
                refine ⟨8808515222164133661907843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11744686962885511549210457 8808515222164133661907843)
                ·
                  refine ⟨13212772833246200492861765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8808515222164133661907843 13212772833246200492861765)
                  ·
                    refine ⟨2477394906233662592411581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13212772833246200492861765 2477394906233662592411581)
                    ·
                      refine ⟨929023089837623472154343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2477394906233662592411581 929023089837623472154343)
                      ·
                        rfl

theorem cell23_1809266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1809266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809266 prefixEnd_1809266 := by exact prefixLift 1809266
  have htrace : WordTrace (prefixWord ++ tailWord_1809266) baseStart_1809266 baseEnd_1809266 := by
    simpa [prefixWord, tailWord_1809266, baseEnd_1809266] using wordTrace_append hprefix tailTrace_1809266
  have hstable : (prefixWord ++ tailWord_1809266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809266).length < 2 ^ (prefixWord ++ tailWord_1809266).sum := by decide
  have hdescent : baseEnd_1809266 < baseStart_1809266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809316 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1809316 : Nat := 118140960795 + 1809316 * 2 ^ 59
def prefixEnd_1809316 : Nat := 4983230072969 + 3 ^ 40 * 1809316 * 2
def baseEnd_1809316 : Nat := 309682921290116092176371

theorem tailTrace_1809316 : CollatzResearch.WordTrace tailWord_1809316 prefixEnd_1809316 309682921290116092176371 := by
  unfold tailWord_1809316
  simp only [CollatzResearch.WordTrace]
  refine ⟨32995587956582306708319901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43994117275443075611093201 32995587956582306708319901)
  ·
    refine ⟨12373345483718365015619963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32995587956582306708319901 12373345483718365015619963)
    ·
      refine ⟨18560018225577547523429945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12373345483718365015619963 18560018225577547523429945)
      ·
        refine ⟨13920013669183160642572459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18560018225577547523429945 13920013669183160642572459)
        ·
          refine ⟨20880020503774740963858689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13920013669183160642572459 20880020503774740963858689)
          ·
            refine ⟨15660015377831055722894017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20880020503774740963858689 15660015377831055722894017)
            ·
              refine ⟨11745011533373291792170513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15660015377831055722894017 11745011533373291792170513)
              ·
                refine ⟨8808758650029968844127885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11745011533373291792170513 8808758650029968844127885)
                ·
                  refine ⟨3303284493761238316547957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8808758650029968844127885 3303284493761238316547957)
                  ·
                    refine ⟨309682921290116092176371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3303284493761238316547957 309682921290116092176371)
                    ·
                      rfl

theorem cell23_1809316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1809316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809316 prefixEnd_1809316 := by exact prefixLift 1809316
  have htrace : WordTrace (prefixWord ++ tailWord_1809316) baseStart_1809316 baseEnd_1809316 := by
    simpa [prefixWord, tailWord_1809316, baseEnd_1809316] using wordTrace_append hprefix tailTrace_1809316
  have hstable : (prefixWord ++ tailWord_1809316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809316).length < 2 ^ (prefixWord ++ tailWord_1809316).sum := by decide
  have hdescent : baseEnd_1809316 < baseStart_1809316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809359 : List Nat := [1, 1, 2, 1, 1, 17]
def baseStart_1809359 : Nat := 118140960795 + 1809359 * 2 ^ 59
def prefixEnd_1809359 : Nat := 4983230072969 + 3 ^ 40 * 1809359 * 2
def baseEnd_1809359 : Nat := 3823336804685150651405

theorem tailTrace_1809359 : CollatzResearch.WordTrace tailWord_1809359 prefixEnd_1809359 3823336804685150651405 := by
  unfold tailWord_1809359
  simp only [CollatzResearch.WordTrace]
  refine ⟨65992744252008831760455131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43995162834672554506970087 65992744252008831760455131)
  ·
    refine ⟨98989116378013247640682697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65992744252008831760455131 98989116378013247640682697)
    ·
      refine ⟨74241837283509935730512023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98989116378013247640682697 74241837283509935730512023)
      ·
        refine ⟨111362755925264903595768035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74241837283509935730512023 111362755925264903595768035)
        ·
          refine ⟨167044133887897355393652053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111362755925264903595768035 167044133887897355393652053)
          ·
            refine ⟨3823336804685150651405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 17 167044133887897355393652053 3823336804685150651405)
            ·
              rfl

theorem cell23_1809359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 17].length) (baseStart_1809359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809359 prefixEnd_1809359 := by exact prefixLift 1809359
  have htrace : WordTrace (prefixWord ++ tailWord_1809359) baseStart_1809359 baseEnd_1809359 := by
    simpa [prefixWord, tailWord_1809359, baseEnd_1809359] using wordTrace_append hprefix tailTrace_1809359
  have hstable : (prefixWord ++ tailWord_1809359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809359).length < 2 ^ (prefixWord ++ tailWord_1809359).sum := by decide
  have hdescent : baseEnd_1809359 < baseStart_1809359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809364 : List Nat := [2, 4, 1, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_1809364 : Nat := 118140960795 + 1809364 * 2 ^ 59
def prefixEnd_1809364 : Nat := 4983230072969 + 3 ^ 40 * 1809364 * 2
def baseEnd_1809364 : Nat := 929073410941764088728893

theorem tailTrace_1809364 : CollatzResearch.WordTrace tailWord_1809364 prefixEnd_1809364 929073410941764088728893 := by
  unfold tailWord_1809364
  simp only [CollatzResearch.WordTrace]
  refine ⟨32996463308495358807193573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43995284411327145076258097 32996463308495358807193573)
  ·
    refine ⟨6186836870342879776348795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32996463308495358807193573 6186836870342879776348795)
    ·
      refine ⟨9280255305514319664523193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6186836870342879776348795 9280255305514319664523193)
      ·
        refine ⟨6960191479135739748392395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9280255305514319664523193 6960191479135739748392395)
        ·
          refine ⟨10440287218703609622588593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6960191479135739748392395 10440287218703609622588593)
          ·
            refine ⟨7830215414027707216941445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10440287218703609622588593 7830215414027707216941445)
            ·
              refine ⟨1468165390130195103176521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7830215414027707216941445 1468165390130195103176521)
              ·
                refine ⟨1101124042597646327382391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468165390130195103176521 1101124042597646327382391)
                ·
                  refine ⟨1651686063896469491073587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101124042597646327382391 1651686063896469491073587)
                  ·
                    refine ⟨2477529095844704236610381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1651686063896469491073587 2477529095844704236610381)
                    ·
                      refine ⟨929073410941764088728893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2477529095844704236610381 929073410941764088728893)
                      ·
                        rfl

theorem cell23_1809364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_1809364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809364 prefixEnd_1809364 := by exact prefixLift 1809364
  have htrace : WordTrace (prefixWord ++ tailWord_1809364) baseStart_1809364 baseEnd_1809364 := by
    simpa [prefixWord, tailWord_1809364, baseEnd_1809364] using wordTrace_append hprefix tailTrace_1809364
  have hstable : (prefixWord ++ tailWord_1809364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809364).length < 2 ^ (prefixWord ++ tailWord_1809364).sum := by decide
  have hdescent : baseEnd_1809364 < baseStart_1809364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809383 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1809383 : Nat := 118140960795 + 1809383 * 2 ^ 59
def prefixEnd_1809383 : Nat := 4983230072969 + 3 ^ 40 * 1809383 * 2
def baseEnd_1809383 : Nat := 929083167074199514391305

theorem tailTrace_1809383 : CollatzResearch.WordTrace tailWord_1809383 prefixEnd_1809383 929083167074199514391305 := by
  unfold tailWord_1809383
  simp only [CollatzResearch.WordTrace]
  refine ⟨65993619603921883859328803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43995746402614589239552535 65993619603921883859328803)
  ·
    refine ⟨98990429405882825788993205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65993619603921883859328803 98990429405882825788993205)
    ·
      refine ⟨9280352756801514917718113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98990429405882825788993205 9280352756801514917718113)
      ·
        refine ⟨6960264567601136188288585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9280352756801514917718113 6960264567601136188288585)
        ·
          refine ⟨5220198425700852141216439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6960264567601136188288585 5220198425700852141216439)
          ·
            refine ⟨7830297638551278211824659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220198425700852141216439 7830297638551278211824659)
            ·
              refine ⟨11745446457826917317736989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830297638551278211824659 11745446457826917317736989)
              ·
                refine ⟨4404542421685093994151371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11745446457826917317736989 4404542421685093994151371)
                ·
                  refine ⟨6606813632527640991227057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404542421685093994151371 6606813632527640991227057)
                  ·
                    refine ⟨4955110224395730743420293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6606813632527640991227057 4955110224395730743420293)
                    ·
                      refine ⟨929083167074199514391305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4955110224395730743420293 929083167074199514391305)
                      ·
                        rfl

theorem cell23_1809383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1809383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809383 prefixEnd_1809383 := by exact prefixLift 1809383
  have htrace : WordTrace (prefixWord ++ tailWord_1809383) baseStart_1809383 baseEnd_1809383 := by
    simpa [prefixWord, tailWord_1809383, baseEnd_1809383] using wordTrace_append hprefix tailTrace_1809383
  have hstable : (prefixWord ++ tailWord_1809383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809383).length < 2 ^ (prefixWord ++ tailWord_1809383).sum := by decide
  have hdescent : baseEnd_1809383 < baseStart_1809383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809393 : List Nat := [1, 2, 2, 2, 4, 2, 3, 7]
def baseStart_1809393 : Nat := 118140960795 + 1809393 * 2 ^ 59
def prefixEnd_1809393 : Nat := 4983230072969 + 3 ^ 40 * 1809393 * 2
def baseEnd_1809393 : Nat := 34410677847434980565417

theorem tailTrace_1809393 : CollatzResearch.WordTrace tailWord_1809393 prefixEnd_1809393 34410677847434980565417 := by
  unfold tailWord_1809393
  simp only [CollatzResearch.WordTrace]
  refine ⟨65993984333885655567192833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43995989555923770378128555 65993984333885655567192833)
  ·
    refine ⟨49495488250414241675394625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65993984333885655567192833 49495488250414241675394625)
    ·
      refine ⟨37121616187810681256545969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49495488250414241675394625 37121616187810681256545969)
      ·
        refine ⟨27841212140858010942409477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37121616187810681256545969 27841212140858010942409477)
        ·
          refine ⟨5220227276410877051701777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27841212140858010942409477 5220227276410877051701777)
          ·
            refine ⟨3915170457308157788776333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5220227276410877051701777 3915170457308157788776333)
            ·
              refine ⟨1468188921490559170791125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3915170457308157788776333 1468188921490559170791125)
              ·
                refine ⟨34410677847434980565417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1468188921490559170791125 34410677847434980565417)
                ·
                  rfl

theorem cell23_1809393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 7].length) (baseStart_1809393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809393 prefixEnd_1809393 := by exact prefixLift 1809393
  have htrace : WordTrace (prefixWord ++ tailWord_1809393) baseStart_1809393 baseEnd_1809393 := by
    simpa [prefixWord, tailWord_1809393, baseEnd_1809393] using wordTrace_append hprefix tailTrace_1809393
  have hstable : (prefixWord ++ tailWord_1809393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809393).length < 2 ^ (prefixWord ++ tailWord_1809393).sum := by decide
  have hdescent : baseEnd_1809393 < baseStart_1809393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809403 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 3]
def baseStart_1809403 : Nat := 118140960795 + 1809403 * 2 ^ 59
def prefixEnd_1809403 : Nat := 4983230072969 + 3 ^ 40 * 1809403 * 2
def baseEnd_1809403 : Nat := 929093436687289436141213

theorem tailTrace_1809403 : CollatzResearch.WordTrace tailWord_1809403 prefixEnd_1809403 929093436687289436141213 := by
  unfold tailWord_1809403
  simp only [CollatzResearch.WordTrace]
  refine ⟨65994349063849427275056863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43996232709232951516704575 65994349063849427275056863)
  ·
    refine ⟨98991523595774140912585295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65994349063849427275056863 98991523595774140912585295)
    ·
      refine ⟨148487285393661211368877943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98991523595774140912585295 148487285393661211368877943)
      ·
        refine ⟨222730928090491817053316915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148487285393661211368877943 222730928090491817053316915)
        ·
          refine ⟨334096392135737725579975373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222730928090491817053316915 334096392135737725579975373)
          ·
            refine ⟨125286147050901647092490765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334096392135737725579975373 125286147050901647092490765)
            ·
              refine ⟨46982305144088117659684037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125286147050901647092490765 46982305144088117659684037)
              ·
                refine ⟨8809182214516522061190757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46982305144088117659684037 8809182214516522061190757)
                ·
                  refine ⟨1651721665221847886473267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8809182214516522061190757 1651721665221847886473267)
                  ·
                    refine ⟨2477582497832771829709901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1651721665221847886473267 2477582497832771829709901)
                    ·
                      refine ⟨929093436687289436141213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2477582497832771829709901 929093436687289436141213)
                      ·
                        rfl

theorem cell23_1809403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 3].length) (baseStart_1809403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809403 prefixEnd_1809403 := by exact prefixLift 1809403
  have htrace : WordTrace (prefixWord ++ tailWord_1809403) baseStart_1809403 baseEnd_1809403 := by
    simpa [prefixWord, tailWord_1809403, baseEnd_1809403] using wordTrace_append hprefix tailTrace_1809403
  have hstable : (prefixWord ++ tailWord_1809403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809403).length < 2 ^ (prefixWord ++ tailWord_1809403).sum := by decide
  have hdescent : baseEnd_1809403 < baseStart_1809403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809404 : List Nat := [2, 2, 2, 1, 2, 4, 2, 3, 1, 2, 2]
def baseStart_1809404 : Nat := 118140960795 + 1809404 * 2 ^ 59
def prefixEnd_1809404 : Nat := 4983230072969 + 3 ^ 40 * 1809404 * 2
def baseEnd_1809404 : Nat := 929093950167943932228709

theorem tailTrace_1809404 : CollatzResearch.WordTrace tailWord_1809404 prefixEnd_1809404 929093950167943932228709 := by
  unfold tailWord_1809404
  simp only [CollatzResearch.WordTrace]
  refine ⟨32997192768422902222921633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43996257024563869630562177 32997192768422902222921633)
  ·
    refine ⟨24747894576317176667191225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32997192768422902222921633 24747894576317176667191225)
    ·
      refine ⟨18560920932237882500393419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24747894576317176667191225 18560920932237882500393419)
      ·
        refine ⟨27841381398356823750590129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18560920932237882500393419 27841381398356823750590129)
        ·
          refine ⟨20881036048767617812942597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27841381398356823750590129 20881036048767617812942597)
          ·
            refine ⟨3915194259143928339926737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20881036048767617812942597 3915194259143928339926737)
            ·
              refine ⟨2936395694357946254945053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3915194259143928339926737 2936395694357946254945053)
              ·
                refine ⟨1101148385384229845604395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2936395694357946254945053 1101148385384229845604395)
                ·
                  refine ⟨1651722578076344768406593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101148385384229845604395 1651722578076344768406593)
                  ·
                    refine ⟨1238791933557258576304945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1651722578076344768406593 1238791933557258576304945)
                    ·
                      refine ⟨929093950167943932228709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1238791933557258576304945 929093950167943932228709)
                      ·
                        rfl

theorem cell23_1809404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_1809404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809404 prefixEnd_1809404 := by exact prefixLift 1809404
  have htrace : WordTrace (prefixWord ++ tailWord_1809404) baseStart_1809404 baseEnd_1809404 := by
    simpa [prefixWord, tailWord_1809404, baseEnd_1809404] using wordTrace_append hprefix tailTrace_1809404
  have hstable : (prefixWord ++ tailWord_1809404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809404).length < 2 ^ (prefixWord ++ tailWord_1809404).sum := by decide
  have hdescent : baseEnd_1809404 < baseStart_1809404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809410 : List Nat := [3, 4, 1, 3, 1, 1, 10]
def baseStart_1809410 : Nat := 118140960795 + 1809410 * 2 ^ 59
def prefixEnd_1809410 : Nat := 4983230072969 + 3 ^ 40 * 1809410 * 2
def baseEnd_1809410 : Nat := 11470333716689764305601

theorem tailTrace_1809410 : CollatzResearch.WordTrace tailWord_1809410 prefixEnd_1809410 11470333716689764305601 := by
  unfold tailWord_1809410
  simp only [CollatzResearch.WordTrace]
  refine ⟨16498651093706016867640421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43996402916549378313707789 16498651093706016867640421)
  ·
    refine ⟨3093497080069878162682579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16498651093706016867640421 3093497080069878162682579)
    ·
      refine ⟨4640245620104817244023869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3093497080069878162682579 4640245620104817244023869)
      ·
        refine ⟨1740092107539306466508951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4640245620104817244023869 1740092107539306466508951)
        ·
          refine ⟨2610138161308959699763427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740092107539306466508951 2610138161308959699763427)
          ·
            refine ⟨3915207241963439549645141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610138161308959699763427 3915207241963439549645141)
            ·
              refine ⟨11470333716689764305601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3915207241963439549645141 11470333716689764305601)
              ·
                rfl

theorem cell23_1809410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 10].length) (baseStart_1809410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809410 prefixEnd_1809410 := by exact prefixLift 1809410
  have htrace : WordTrace (prefixWord ++ tailWord_1809410) baseStart_1809410 baseEnd_1809410 := by
    simpa [prefixWord, tailWord_1809410, baseEnd_1809410] using wordTrace_append hprefix tailTrace_1809410
  have hstable : (prefixWord ++ tailWord_1809410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809410).length < 2 ^ (prefixWord ++ tailWord_1809410).sum := by decide
  have hdescent : baseEnd_1809410 < baseStart_1809410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809420 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 4, 1, 3]
def baseStart_1809420 : Nat := 118140960795 + 1809420 * 2 ^ 59
def prefixEnd_1809420 : Nat := 4983230072969 + 3 ^ 40 * 1809420 * 2
def baseEnd_1809420 : Nat := 929102165858415869628635

theorem tailTrace_1809420 : CollatzResearch.WordTrace tailWord_1809420 prefixEnd_1809420 929102165858415869628635 := by
  unfold tailWord_1809420
  simp only [CollatzResearch.WordTrace]
  refine ⟨32997484552393919589212857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43996646069858559452283809 32997484552393919589212857)
  ·
    refine ⟨24748113414295439691909643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32997484552393919589212857 24748113414295439691909643)
    ·
      refine ⟨37122170121443159537864465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24748113414295439691909643 37122170121443159537864465)
      ·
        refine ⟨27841627591082369653398349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37122170121443159537864465 27841627591082369653398349)
        ·
          refine ⟨10440610346655888620024381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27841627591082369653398349 10440610346655888620024381)
          ·
            refine ⟨3915228879995958232509143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10440610346655888620024381 3915228879995958232509143)
            ·
              refine ⟨5872843319993937348763715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915228879995958232509143 5872843319993937348763715)
              ·
                refine ⟨8809264979990906023145573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5872843319993937348763715 8809264979990906023145573)
                ·
                  refine ⟨1651737183748294879339795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8809264979990906023145573 1651737183748294879339795)
                  ·
                    refine ⟨2477605775622442319009693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1651737183748294879339795 2477605775622442319009693)
                    ·
                      refine ⟨929102165858415869628635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2477605775622442319009693 929102165858415869628635)
                      ·
                        rfl

theorem cell23_1809420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_1809420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809420 prefixEnd_1809420 := by exact prefixLift 1809420
  have htrace : WordTrace (prefixWord ++ tailWord_1809420) baseStart_1809420 baseEnd_1809420 := by
    simpa [prefixWord, tailWord_1809420, baseEnd_1809420] using wordTrace_append hprefix tailTrace_1809420
  have hstable : (prefixWord ++ tailWord_1809420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809420).length < 2 ^ (prefixWord ++ tailWord_1809420).sum := by decide
  have hdescent : baseEnd_1809420 < baseStart_1809420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809437 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1809437 : Nat := 118140960795 + 1809437 * 2 ^ 59
def prefixEnd_1809437 : Nat := 4983230072969 + 3 ^ 40 * 1809437 * 2
def baseEnd_1809437 : Nat := 929110895029542303116057

theorem tailTrace_1809437 : CollatzResearch.WordTrace tailWord_1809437 prefixEnd_1809437 929110895029542303116057 := by
  unfold tailWord_1809437
  simp only [CollatzResearch.WordTrace]
  refine ⟨65995589145726251081794565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43997059430484167387863043 65995589145726251081794565)
  ·
    refine ⟨12374172964823672077836481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65995589145726251081794565 12374172964823672077836481)
    ·
      refine ⟨9280629723617754058377361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12374172964823672077836481 9280629723617754058377361)
      ·
        refine ⟨6960472292713315543783021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9280629723617754058377361 6960472292713315543783021)
        ·
          refine ⟨2610177109767493328918633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6960472292713315543783021 2610177109767493328918633)
          ·
            refine ⟨1957632832325619996688975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2610177109767493328918633 1957632832325619996688975)
            ·
              refine ⟨2936449248488429995033463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957632832325619996688975 2936449248488429995033463)
              ·
                refine ⟨4404673872732644992550195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936449248488429995033463 4404673872732644992550195)
                ·
                  refine ⟨6607010809098967488825293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404673872732644992550195 6607010809098967488825293)
                  ·
                    refine ⟨2477629053412112808309485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6607010809098967488825293 2477629053412112808309485)
                    ·
                      refine ⟨929110895029542303116057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2477629053412112808309485 929110895029542303116057)
                      ·
                        rfl

theorem cell23_1809437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1809437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809437 prefixEnd_1809437 := by exact prefixLift 1809437
  have htrace : WordTrace (prefixWord ++ tailWord_1809437) baseStart_1809437 baseEnd_1809437 := by
    simpa [prefixWord, tailWord_1809437, baseEnd_1809437] using wordTrace_append hprefix tailTrace_1809437
  have hstable : (prefixWord ++ tailWord_1809437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809437).length < 2 ^ (prefixWord ++ tailWord_1809437).sum := by decide
  have hdescent : baseEnd_1809437 < baseStart_1809437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809466 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 9]
def baseStart_1809466 : Nat := 118140960795 + 1809466 * 2 ^ 59
def prefixEnd_1809466 : Nat := 4983230072969 + 3 ^ 40 * 1809466 * 2
def baseEnd_1809466 : Nat := 103236198440946965517047

theorem tailTrace_1809466 : CollatzResearch.WordTrace tailWord_1809466 prefixEnd_1809466 103236198440946965517047 := by
  unfold tailWord_1809466
  simp only [CollatzResearch.WordTrace]
  refine ⟨16499161715655297258650063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43997764575080792689733501 16499161715655297258650063)
  ·
    refine ⟨24748742573482945887975095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16499161715655297258650063 24748742573482945887975095)
    ·
      refine ⟨37123113860224418831962643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24748742573482945887975095 37123113860224418831962643)
      ·
        refine ⟨55684670790336628247943965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37123113860224418831962643 55684670790336628247943965)
        ·
          refine ⟨20881751546376235592978987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55684670790336628247943965 20881751546376235592978987)
          ·
            refine ⟨31322627319564353389468481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20881751546376235592978987 31322627319564353389468481)
            ·
              refine ⟨23491970489673265042101361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31322627319564353389468481 23491970489673265042101361)
              ·
                refine ⟨17618977867254948781576021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23491970489673265042101361 17618977867254948781576021)
                ·
                  refine ⟨103236198440946965517047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17618977867254948781576021 103236198440946965517047)
                  ·
                    rfl

theorem cell23_1809466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_1809466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809466 prefixEnd_1809466 := by exact prefixLift 1809466
  have htrace : WordTrace (prefixWord ++ tailWord_1809466) baseStart_1809466 baseEnd_1809466 := by
    simpa [prefixWord, tailWord_1809466, baseEnd_1809466] using wordTrace_append hprefix tailTrace_1809466
  have hstable : (prefixWord ++ tailWord_1809466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809466).length < 2 ^ (prefixWord ++ tailWord_1809466).sum := by decide
  have hdescent : baseEnd_1809466 < baseStart_1809466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809493 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1809493 : Nat := 118140960795 + 1809493 * 2 ^ 59
def prefixEnd_1809493 : Nat := 4983230072969 + 3 ^ 40 * 1809493 * 2
def baseEnd_1809493 : Nat := 929139649946194084015799

theorem tailTrace_1809493 : CollatzResearch.WordTrace tailWord_1809493 prefixEnd_1809493 929139649946194084015799 := by
  unfold tailWord_1809493
  simp only [CollatzResearch.WordTrace]
  refine ⟨65997631633523372645833133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43998421089015581763888755 65997631633523372645833133)
  ·
    refine ⟨24749111862571264742187425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65997631633523372645833133 24749111862571264742187425)
    ·
      refine ⟨18561833896928448556640569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24749111862571264742187425 18561833896928448556640569)
      ·
        refine ⟨13921375422696336417480427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18561833896928448556640569 13921375422696336417480427)
        ·
          refine ⟨20882063134044504626220641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13921375422696336417480427 20882063134044504626220641)
          ·
            refine ⟨15661547350533378469665481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20882063134044504626220641 15661547350533378469665481)
            ·
              refine ⟨11746160512900033852249111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15661547350533378469665481 11746160512900033852249111)
              ·
                refine ⟨17619240769350050778373667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11746160512900033852249111 17619240769350050778373667)
                ·
                  refine ⟨26428861154025076167560501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17619240769350050778373667 26428861154025076167560501)
                  ·
                    refine ⟨2477705733189850890708797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26428861154025076167560501 2477705733189850890708797)
                    ·
                      refine ⟨929139649946194084015799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2477705733189850890708797 929139649946194084015799)
                      ·
                        rfl

theorem cell23_1809493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1809493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809493 prefixEnd_1809493 := by exact prefixLift 1809493
  have htrace : WordTrace (prefixWord ++ tailWord_1809493) baseStart_1809493 baseEnd_1809493 := by
    simpa [prefixWord, tailWord_1809493, baseEnd_1809493] using wordTrace_append hprefix tailTrace_1809493
  have hstable : (prefixWord ++ tailWord_1809493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809493).length < 2 ^ (prefixWord ++ tailWord_1809493).sum := by decide
  have hdescent : baseEnd_1809493 < baseStart_1809493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809513 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 2, 5]
def baseStart_1809513 : Nat := 118140960795 + 1809513 * 2 ^ 59
def prefixEnd_1809513 : Nat := 4983230072969 + 3 ^ 40 * 1809513 * 2
def baseEnd_1809513 : Nat := 309716639853094668588569

theorem tailTrace_1809513 : CollatzResearch.WordTrace tailWord_1809513 prefixEnd_1809513 309716639853094668588569 := by
  unfold tailWord_1809513
  simp only [CollatzResearch.WordTrace]
  refine ⟨65998361093450916061561193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43998907395633944041040795 65998361093450916061561193)
  ·
    refine ⟨49498770820088187046170895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65998361093450916061561193 49498770820088187046170895)
    ·
      refine ⟨74248156230132280569256343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49498770820088187046170895 74248156230132280569256343)
      ·
        refine ⟨111372234345198420853884515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74248156230132280569256343 111372234345198420853884515)
        ·
          refine ⟨167058351517797631280826773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111372234345198420853884515 167058351517797631280826773)
          ·
            refine ⟨7830860227396763966288755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167058351517797631280826773 7830860227396763966288755)
            ·
              refine ⟨11746290341095145949433133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830860227396763966288755 11746290341095145949433133)
              ·
                refine ⟨4404858877910679731037425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11746290341095145949433133 4404858877910679731037425)
                ·
                  refine ⟨3303644158433009798278069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4404858877910679731037425 3303644158433009798278069)
                  ·
                    refine ⟨309716639853094668588569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3303644158433009798278069 309716639853094668588569)
                    ·
                      rfl

theorem cell23_1809513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_1809513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809513 prefixEnd_1809513 := by exact prefixLift 1809513
  have htrace : WordTrace (prefixWord ++ tailWord_1809513) baseStart_1809513 baseEnd_1809513 := by
    simpa [prefixWord, tailWord_1809513, baseEnd_1809513] using wordTrace_append hprefix tailTrace_1809513
  have hstable : (prefixWord ++ tailWord_1809513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809513).length < 2 ^ (prefixWord ++ tailWord_1809513).sum := by decide
  have hdescent : baseEnd_1809513 < baseStart_1809513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809560 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 5, 4]
def baseStart_1809560 : Nat := 118140960795 + 1809560 * 2 ^ 59
def prefixEnd_1809560 : Nat := 4983230072969 + 3 ^ 40 * 1809560 * 2
def baseEnd_1809560 : Nat := 309724684383348440625997

theorem tailTrace_1809560 : CollatzResearch.WordTrace tailWord_1809560 prefixEnd_1809560 309724684383348440625997 := by
  unfold tailWord_1809560
  simp only [CollatzResearch.WordTrace]
  refine ⟨33000037662140321544261067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44000050216187095392348089 33000037662140321544261067)
  ·
    refine ⟨49500056493210482316391601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33000037662140321544261067 49500056493210482316391601)
    ·
      refine ⟨37125042369907861737293701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49500056493210482316391601 37125042369907861737293701)
      ·
        refine ⟨6960945444357724075742569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37125042369907861737293701 6960945444357724075742569)
        ·
          refine ⟨5220709083268293056806927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6960945444357724075742569 5220709083268293056806927)
          ·
            refine ⟨7831063624902439585210391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220709083268293056806927 7831063624902439585210391)
            ·
              refine ⟨11746595437353659377815587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831063624902439585210391 11746595437353659377815587)
              ·
                refine ⟨17619893156030489066723381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11746595437353659377815587 17619893156030489066723381)
                ·
                  refine ⟨1651864983377858350005317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17619893156030489066723381 1651864983377858350005317)
                  ·
                    refine ⟨309724684383348440625997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1651864983377858350005317 309724684383348440625997)
                    ·
                      rfl

theorem cell23_1809560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_1809560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809560 prefixEnd_1809560 := by exact prefixLift 1809560
  have htrace : WordTrace (prefixWord ++ tailWord_1809560) baseStart_1809560 baseEnd_1809560 := by
    simpa [prefixWord, tailWord_1809560, baseEnd_1809560] using wordTrace_append hprefix tailTrace_1809560
  have hstable : (prefixWord ++ tailWord_1809560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809560).length < 2 ^ (prefixWord ++ tailWord_1809560).sum := by decide
  have hdescent : baseEnd_1809560 < baseStart_1809560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809593 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1809593 : Nat := 118140960795 + 1809593 * 2 ^ 59
def prefixEnd_1809593 : Nat := 4983230072969 + 3 ^ 40 * 1809593 * 2
def baseEnd_1809593 : Nat := 929190998011643692765339

theorem tailTrace_1809593 : CollatzResearch.WordTrace tailWord_1809593 prefixEnd_1809593 929190998011643692765339 := by
  unfold tailWord_1809593
  simp only [CollatzResearch.WordTrace]
  refine ⟨66001278933161089724473433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44000852622107393149648955 66001278933161089724473433)
  ·
    refine ⟨49500959199870817293355075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66001278933161089724473433 49500959199870817293355075)
    ·
      refine ⟨74251438799806225940032613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49500959199870817293355075 74251438799806225940032613)
      ·
        refine ⟨13922144774963667363756115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74251438799806225940032613 13922144774963667363756115)
        ·
          refine ⟨20883217162445501045634173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13922144774963667363756115 20883217162445501045634173)
          ·
            refine ⟨7831206435917062892112815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20883217162445501045634173 7831206435917062892112815)
            ·
              refine ⟨11746809653875594338169223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831206435917062892112815 11746809653875594338169223)
              ·
                refine ⟨17620214480813391507253835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11746809653875594338169223 17620214480813391507253835)
                ·
                  refine ⟨26430321721220087260880753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17620214480813391507253835 26430321721220087260880753)
                  ·
                    refine ⟨19822741290915065445660565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26430321721220087260880753 19822741290915065445660565)
                    ·
                      refine ⟨929190998011643692765339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19822741290915065445660565 929190998011643692765339)
                      ·
                        rfl

theorem cell23_1809593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1809593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809593 prefixEnd_1809593 := by exact prefixLift 1809593
  have htrace : WordTrace (prefixWord ++ tailWord_1809593) baseStart_1809593 baseEnd_1809593 := by
    simpa [prefixWord, tailWord_1809593, baseEnd_1809593] using wordTrace_append hprefix tailTrace_1809593
  have hstable : (prefixWord ++ tailWord_1809593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809593).length < 2 ^ (prefixWord ++ tailWord_1809593).sum := by decide
  have hdescent : baseEnd_1809593 < baseStart_1809593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809603 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 3, 5]
def baseStart_1809603 : Nat := 118140960795 + 1809603 * 2 ^ 59
def prefixEnd_1809603 : Nat := 4983230072969 + 3 ^ 40 * 1809603 * 2
def baseEnd_1809603 : Nat := 309732044272729551213431

theorem tailTrace_1809603 : CollatzResearch.WordTrace tailWord_1809603 prefixEnd_1809603 309732044272729551213431 := by
  unfold tailWord_1809603
  simp only [CollatzResearch.WordTrace]
  refine ⟨66001643663124861432337463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44001095775416574288224975 66001643663124861432337463)
  ·
    refine ⟨99002465494687292148506195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66001643663124861432337463 99002465494687292148506195)
    ·
      refine ⟨148503698242030938222759293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99002465494687292148506195 148503698242030938222759293)
      ·
        refine ⟨55688886840761601833534735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148503698242030938222759293 55688886840761601833534735)
        ·
          refine ⟨83533330261142402750302103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55688886840761601833534735 83533330261142402750302103)
          ·
            refine ⟨125299995391713604125453155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83533330261142402750302103 125299995391713604125453155)
            ·
              refine ⟨187949993087570406188179733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125299995391713604125453155 187949993087570406188179733)
              ·
                refine ⟨8810155925979862790070925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187949993087570406188179733 8810155925979862790070925)
                ·
                  refine ⟨3303808472242448546276597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8810155925979862790070925 3303808472242448546276597)
                  ·
                    refine ⟨309732044272729551213431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3303808472242448546276597 309732044272729551213431)
                    ·
                      rfl

theorem cell23_1809603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 5].length) (baseStart_1809603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809603 prefixEnd_1809603 := by exact prefixLift 1809603
  have htrace : WordTrace (prefixWord ++ tailWord_1809603) baseStart_1809603 baseEnd_1809603 := by
    simpa [prefixWord, tailWord_1809603, baseEnd_1809603] using wordTrace_append hprefix tailTrace_1809603
  have hstable : (prefixWord ++ tailWord_1809603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809603).length < 2 ^ (prefixWord ++ tailWord_1809603).sum := by decide
  have hdescent : baseEnd_1809603 < baseStart_1809603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809651 : List Nat := [1, 1, 1, 2, 2, 6, 3, 2, 1, 1, 3]
def baseStart_1809651 : Nat := 118140960795 + 1809651 * 2 ^ 59
def prefixEnd_1809651 : Nat := 4983230072969 + 3 ^ 40 * 1809651 * 2
def baseEnd_1809651 : Nat := 929220779889604465840073

theorem tailTrace_1809651 : CollatzResearch.WordTrace tailWord_1809651 prefixEnd_1809651 929220779889604465840073 := by
  unfold tailWord_1809651
  simp only [CollatzResearch.WordTrace]
  refine ⟨66003394366950965630084807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44002262911300643753389871 66003394366950965630084807)
  ·
    refine ⟨99005091550426448445127211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66003394366950965630084807 99005091550426448445127211)
    ·
      refine ⟨148507637325639672667690817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99005091550426448445127211 148507637325639672667690817)
      ·
        refine ⟨111380727994229754500768113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148507637325639672667690817 111380727994229754500768113)
        ·
          refine ⟨83535545995672315875576085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111380727994229754500768113 83535545995672315875576085)
          ·
            refine ⟨3915728718547139806667629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83535545995672315875576085 3915728718547139806667629)
            ·
              refine ⟨1468398269455177427500361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3915728718547139806667629 1468398269455177427500361)
              ·
                refine ⟨1101298702091383070625271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468398269455177427500361 1101298702091383070625271)
                ·
                  refine ⟨1651948053137074605937907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101298702091383070625271 1651948053137074605937907)
                  ·
                    refine ⟨2477922079705611908906861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1651948053137074605937907 2477922079705611908906861)
                    ·
                      refine ⟨929220779889604465840073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2477922079705611908906861 929220779889604465840073)
                      ·
                        rfl

theorem cell23_1809651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 1, 3].length) (baseStart_1809651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809651 prefixEnd_1809651 := by exact prefixLift 1809651
  have htrace : WordTrace (prefixWord ++ tailWord_1809651) baseStart_1809651 baseEnd_1809651 := by
    simpa [prefixWord, tailWord_1809651, baseEnd_1809651] using wordTrace_append hprefix tailTrace_1809651
  have hstable : (prefixWord ++ tailWord_1809651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809651).length < 2 ^ (prefixWord ++ tailWord_1809651).sum := by decide
  have hdescent : baseEnd_1809651 < baseStart_1809651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809663 : List Nat := [1, 1, 2, 2, 1, 5, 1, 10]
def baseStart_1809663 : Nat := 118140960795 + 1809663 * 2 ^ 59
def prefixEnd_1809663 : Nat := 4983230072969 + 3 ^ 40 * 1809663 * 2
def baseEnd_1809663 : Nat := 34415812653979941440371

theorem tailTrace_1809663 : CollatzResearch.WordTrace tailWord_1809663 prefixEnd_1809663 34415812653979941440371 := by
  unfold tailWord_1809663
  simp only [CollatzResearch.WordTrace]
  refine ⟨66003832042907491679521643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44002554695271661119681095 66003832042907491679521643)
  ·
    refine ⟨99005748064361237519282465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66003832042907491679521643 99005748064361237519282465)
    ·
      refine ⟨74254311048270928139461849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99005748064361237519282465 74254311048270928139461849)
      ·
        refine ⟨55690733286203196104596387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74254311048270928139461849 55690733286203196104596387)
        ·
          refine ⟨83536099929304794156894581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55690733286203196104596387 83536099929304794156894581)
          ·
            refine ⟨7831509368372324452208867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83536099929304794156894581 7831509368372324452208867)
            ·
              refine ⟨11747264052558486678313301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831509368372324452208867 11747264052558486678313301)
              ·
                refine ⟨34415812653979941440371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11747264052558486678313301 34415812653979941440371)
                ·
                  rfl

theorem cell23_1809663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 10].length) (baseStart_1809663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809663 prefixEnd_1809663 := by exact prefixLift 1809663
  have htrace : WordTrace (prefixWord ++ tailWord_1809663) baseStart_1809663 baseEnd_1809663 := by
    simpa [prefixWord, tailWord_1809663, baseEnd_1809663] using wordTrace_append hprefix tailTrace_1809663
  have hstable : (prefixWord ++ tailWord_1809663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809663).length < 2 ^ (prefixWord ++ tailWord_1809663).sum := by decide
  have hdescent : baseEnd_1809663 < baseStart_1809663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809667 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 2, 4]
def baseStart_1809667 : Nat := 118140960795 + 1809667 * 2 ^ 59
def prefixEnd_1809667 : Nat := 4983230072969 + 3 ^ 40 * 1809667 * 2
def baseEnd_1809667 : Nat := 309742998526692134413333

theorem tailTrace_1809667 : CollatzResearch.WordTrace tailWord_1809667 prefixEnd_1809667 309742998526692134413333 := by
  unfold tailWord_1809667
  simp only [CollatzResearch.WordTrace]
  refine ⟨66003977934893000362667255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44002651956595333575111503 66003977934893000362667255)
  ·
    refine ⟨99005966902339500544000883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66003977934893000362667255 99005966902339500544000883)
    ·
      refine ⟨148508950353509250816001325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99005966902339500544000883 148508950353509250816001325)
      ·
        refine ⟨55690856382565969056000497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148508950353509250816001325 55690856382565969056000497)
        ·
          refine ⟨41768142286924476792000373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55690856382565969056000497 41768142286924476792000373)
          ·
            refine ⟨3915763339399169699250035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41768142286924476792000373 3915763339399169699250035)
            ·
              refine ⟨5873645009098754548875053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915763339399169699250035 5873645009098754548875053)
              ·
                refine ⟨2202616878412032955828145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5873645009098754548875053 2202616878412032955828145)
                ·
                  refine ⟨1651962658809024716871109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2202616878412032955828145 1651962658809024716871109)
                  ·
                    refine ⟨309742998526692134413333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1651962658809024716871109 309742998526692134413333)
                    ·
                      rfl

theorem cell23_1809667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 4].length) (baseStart_1809667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809667 prefixEnd_1809667 := by exact prefixLift 1809667
  have htrace : WordTrace (prefixWord ++ tailWord_1809667) baseStart_1809667 baseEnd_1809667 := by
    simpa [prefixWord, tailWord_1809667, baseEnd_1809667] using wordTrace_append hprefix tailTrace_1809667
  have hstable : (prefixWord ++ tailWord_1809667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809667).length < 2 ^ (prefixWord ++ tailWord_1809667).sum := by decide
  have hdescent : baseEnd_1809667 < baseStart_1809667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809724 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_1809724 : Nat := 118140960795 + 1809724 * 2 ^ 59
def prefixEnd_1809724 : Nat := 4983230072969 + 3 ^ 40 * 1809724 * 2
def baseEnd_1809724 : Nat := 929258263977382680227237

theorem tailTrace_1809724 : CollatzResearch.WordTrace tailWord_1809724 prefixEnd_1809724 929258263977382680227237 := by
  unfold tailWord_1809724
  simp only [CollatzResearch.WordTrace]
  refine ⟨33003028447843249548746113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44004037930457666064994817 33003028447843249548746113)
  ·
    refine ⟨24752271335882437161559585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33003028447843249548746113 24752271335882437161559585)
    ·
      refine ⟨18564203501911827871169689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24752271335882437161559585 18564203501911827871169689)
      ·
        refine ⟨13923152626433870903377267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18564203501911827871169689 13923152626433870903377267)
        ·
          refine ⟨20884728939650806355065901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13923152626433870903377267 20884728939650806355065901)
          ·
            refine ⟨7831773352369052383149713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20884728939650806355065901 7831773352369052383149713)
            ·
              refine ⟨5873830014276789287362285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7831773352369052383149713 5873830014276789287362285)
              ·
                refine ⟨2202686255353795982760857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5873830014276789287362285 2202686255353795982760857)
                ·
                  refine ⟨1652014691515346987070643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2202686255353795982760857 1652014691515346987070643)
                  ·
                    refine ⟨2478022037273020480605965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1652014691515346987070643 2478022037273020480605965)
                    ·
                      refine ⟨929258263977382680227237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2478022037273020480605965 929258263977382680227237)
                      ·
                        rfl

theorem cell23_1809724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_1809724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809724 prefixEnd_1809724 := by exact prefixLift 1809724
  have htrace : WordTrace (prefixWord ++ tailWord_1809724) baseStart_1809724 baseEnd_1809724 := by
    simpa [prefixWord, tailWord_1809724, baseEnd_1809724] using wordTrace_append hprefix tailTrace_1809724
  have hstable : (prefixWord ++ tailWord_1809724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809724).length < 2 ^ (prefixWord ++ tailWord_1809724).sum := by decide
  have hdescent : baseEnd_1809724 < baseStart_1809724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809747 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 1, 4, 2]
def baseStart_1809747 : Nat := 118140960795 + 1809747 * 2 ^ 59
def prefixEnd_1809747 : Nat := 4983230072969 + 3 ^ 40 * 1809747 * 2
def baseEnd_1809747 : Nat := 929270074032436090239631

theorem tailTrace_1809747 : CollatzResearch.WordTrace tailWord_1809747 prefixEnd_1809747 929270074032436090239631 := by
  unfold tailWord_1809747
  simp only [CollatzResearch.WordTrace]
  refine ⟨66006895774603174025579495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44004597183068782683719663 66006895774603174025579495)
  ·
    refine ⟨99010343661904761038369243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66006895774603174025579495 99010343661904761038369243)
    ·
      refine ⟨148515515492857141557553865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99010343661904761038369243 148515515492857141557553865)
      ·
        refine ⟨111386636619642856168165399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148515515492857141557553865 111386636619642856168165399)
        ·
          refine ⟨167079954929464284252248099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111386636619642856168165399 167079954929464284252248099)
          ·
            refine ⟨250619932394196426378372149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167079954929464284252248099 250619932394196426378372149)
            ·
              refine ⟨23495618661955914972972389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250619932394196426378372149 23495618661955914972972389)
              ·
                refine ⟨4405428499116734057432323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23495618661955914972972389 4405428499116734057432323)
                ·
                  refine ⟨6608142748675101086148485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405428499116734057432323 6608142748675101086148485)
                  ·
                    refine ⟨1239026765376581453652841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6608142748675101086148485 1239026765376581453652841)
                    ·
                      refine ⟨929270074032436090239631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239026765376581453652841 929270074032436090239631)
                      ·
                        rfl

theorem cell23_1809747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 4, 2].length) (baseStart_1809747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809747 prefixEnd_1809747 := by exact prefixLift 1809747
  have htrace : WordTrace (prefixWord ++ tailWord_1809747) baseStart_1809747 baseEnd_1809747 := by
    simpa [prefixWord, tailWord_1809747, baseEnd_1809747] using wordTrace_append hprefix tailTrace_1809747
  have hstable : (prefixWord ++ tailWord_1809747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809747).length < 2 ^ (prefixWord ++ tailWord_1809747).sum := by decide
  have hdescent : baseEnd_1809747 < baseStart_1809747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809751 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 1, 3, 2]
def baseStart_1809751 : Nat := 118140960795 + 1809751 * 2 ^ 59
def prefixEnd_1809751 : Nat := 4983230072969 + 3 ^ 40 * 1809751 * 2
def baseEnd_1809751 : Nat := 929272127955054074589613

theorem tailTrace_1809751 : CollatzResearch.WordTrace tailWord_1809751 prefixEnd_1809751 929272127955054074589613 := by
  unfold tailWord_1809751
  simp only [CollatzResearch.WordTrace]
  refine ⟨66007041666588682708725107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44004694444392455139150071 66007041666588682708725107)
  ·
    refine ⟨99010562499883024063087661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66007041666588682708725107 99010562499883024063087661)
    ·
      refine ⟨37128960937456134023657873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99010562499883024063087661 37128960937456134023657873)
      ·
        refine ⟨27846720703092100517743405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37128960937456134023657873 27846720703092100517743405)
        ·
          refine ⟨10442520263659537694153777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27846720703092100517743405 10442520263659537694153777)
          ·
            refine ⟨7831890197744653270615333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10442520263659537694153777 7831890197744653270615333)
            ·
              refine ⟨1468479412077122488240375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7831890197744653270615333 1468479412077122488240375)
              ·
                refine ⟨2202719118115683732360563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468479412077122488240375 2202719118115683732360563)
                ·
                  refine ⟨3304078677173525598540845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202719118115683732360563 3304078677173525598540845)
                  ·
                    refine ⟨1239029503940072099452817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3304078677173525598540845 1239029503940072099452817)
                    ·
                      refine ⟨929272127955054074589613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239029503940072099452817 929272127955054074589613)
                      ·
                        rfl

theorem cell23_1809751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_1809751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809751 prefixEnd_1809751 := by exact prefixLift 1809751
  have htrace : WordTrace (prefixWord ++ tailWord_1809751) baseStart_1809751 baseEnd_1809751 := by
    simpa [prefixWord, tailWord_1809751, baseEnd_1809751] using wordTrace_append hprefix tailTrace_1809751
  have hstable : (prefixWord ++ tailWord_1809751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809751).length < 2 ^ (prefixWord ++ tailWord_1809751).sum := by decide
  have hdescent : baseEnd_1809751 < baseStart_1809751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809817 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 2, 5]
def baseStart_1809817 : Nat := 118140960795 + 1809817 * 2 ^ 59
def prefixEnd_1809817 : Nat := 4983230072969 + 3 ^ 40 * 1809817 * 2
def baseEnd_1809817 : Nat := 309768672559416938788103

theorem tailTrace_1809817 : CollatzResearch.WordTrace tailWord_1809817 prefixEnd_1809817 309768672559416938788103 := by
  unfold tailWord_1809817
  simp only [CollatzResearch.WordTrace]
  refine ⟨66009448884349575980627705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44006299256233050653751803 66009448884349575980627705)
  ·
    refine ⟨49507086663262181985470779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66009448884349575980627705 49507086663262181985470779)
    ·
      refine ⟨74260629994893272978206169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49507086663262181985470779 74260629994893272978206169)
      ·
        refine ⟨55695472496169954733654627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74260629994893272978206169 55695472496169954733654627)
        ·
          refine ⟨83543208744254932100481941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55695472496169954733654627 83543208744254932100481941)
          ·
            refine ⟨3916087909886949942210091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83543208744254932100481941 3916087909886949942210091)
            ·
              refine ⟨5874131864830424913315137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916087909886949942210091 5874131864830424913315137)
              ·
                refine ⟨4405598898622818684986353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5874131864830424913315137 4405598898622818684986353)
                ·
                  refine ⟨3304199173967114013739765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4405598898622818684986353 3304199173967114013739765)
                  ·
                    refine ⟨309768672559416938788103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3304199173967114013739765 309768672559416938788103)
                    ·
                      rfl

theorem cell23_1809817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_1809817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809817 prefixEnd_1809817 := by exact prefixLift 1809817
  have htrace : WordTrace (prefixWord ++ tailWord_1809817) baseStart_1809817 baseEnd_1809817 := by
    simpa [prefixWord, tailWord_1809817, baseEnd_1809817] using wordTrace_append hprefix tailTrace_1809817
  have hstable : (prefixWord ++ tailWord_1809817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809817).length < 2 ^ (prefixWord ++ tailWord_1809817).sum := by decide
  have hdescent : baseEnd_1809817 < baseStart_1809817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809821 : List Nat := [1, 4, 2, 1, 3, 2, 3, 2, 5]
def baseStart_1809821 : Nat := 118140960795 + 1809821 * 2 ^ 59
def prefixEnd_1809821 : Nat := 4983230072969 + 3 ^ 40 * 1809821 * 2
def baseEnd_1809821 : Nat := 103256452400096533412699

theorem tailTrace_1809821 : CollatzResearch.WordTrace tailWord_1809821 prefixEnd_1809821 103256452400096533412699 := by
  unfold tailWord_1809821
  simp only [CollatzResearch.WordTrace]
  refine ⟨66009594776335084663773317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44006396517556723109182211 66009594776335084663773317)
  ·
    refine ⟨12376799020562828374457497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66009594776335084663773317 12376799020562828374457497)
    ·
      refine ⟨9282599265422121280843123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12376799020562828374457497 9282599265422121280843123)
      ·
        refine ⟨13923898898133181921264685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9282599265422121280843123 13923898898133181921264685)
        ·
          refine ⟨5221462086799943220474257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13923898898133181921264685 5221462086799943220474257)
          ·
            refine ⟨3916096565099957415355693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5221462086799943220474257 3916096565099957415355693)
            ·
              refine ⟨1468536211912484030758385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3916096565099957415355693 1468536211912484030758385)
              ·
                refine ⟨1101402158934363023068789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468536211912484030758385 1101402158934363023068789)
                ·
                  refine ⟨103256452400096533412699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1101402158934363023068789 103256452400096533412699)
                  ·
                    rfl

theorem cell23_1809821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_1809821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809821 prefixEnd_1809821 := by exact prefixLift 1809821
  have htrace : WordTrace (prefixWord ++ tailWord_1809821) baseStart_1809821 baseEnd_1809821 := by
    simpa [prefixWord, tailWord_1809821, baseEnd_1809821] using wordTrace_append hprefix tailTrace_1809821
  have hstable : (prefixWord ++ tailWord_1809821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809821).length < 2 ^ (prefixWord ++ tailWord_1809821).sum := by decide
  have hdescent : baseEnd_1809821 < baseStart_1809821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809832 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1809832 : Nat := 118140960795 + 1809832 * 2 ^ 59
def prefixEnd_1809832 : Nat := 4983230072969 + 3 ^ 40 * 1809832 * 2
def baseEnd_1809832 : Nat := 929313719888068257676741

theorem tailTrace_1809832 : CollatzResearch.WordTrace tailWord_1809832 prefixEnd_1809832 929313719888068257676741 := by
  unfold tailWord_1809832
  simp only [CollatzResearch.WordTrace]
  refine ⟨33004997989647616771211875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44006663986196822361615833 33004997989647616771211875)
  ·
    refine ⟨49507496984471425156817813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33004997989647616771211875 49507496984471425156817813)
    ·
      refine ⟨2320663921147098054225835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49507496984471425156817813 2320663921147098054225835)
      ·
        refine ⟨3480995881720647081338753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320663921147098054225835 3480995881720647081338753)
        ·
          refine ⟨2610746911290485311004065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3480995881720647081338753 2610746911290485311004065)
          ·
            refine ⟨1958060183467863983253049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2610746911290485311004065 1958060183467863983253049)
            ·
              refine ⟨1468545137600897987439787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958060183467863983253049 1468545137600897987439787)
              ·
                refine ⟨2202817706401346981159681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468545137600897987439787 2202817706401346981159681)
                ·
                  refine ⟨1652113279801010235869761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2202817706401346981159681 1652113279801010235869761)
                  ·
                    refine ⟨1239084959850757676902321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1652113279801010235869761 1239084959850757676902321)
                    ·
                      refine ⟨929313719888068257676741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239084959850757676902321 929313719888068257676741)
                      ·
                        rfl

theorem cell23_1809832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1809832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809832 prefixEnd_1809832 := by exact prefixLift 1809832
  have htrace : WordTrace (prefixWord ++ tailWord_1809832) baseStart_1809832 baseEnd_1809832 := by
    simpa [prefixWord, tailWord_1809832, baseEnd_1809832] using wordTrace_append hprefix tailTrace_1809832
  have hstable : (prefixWord ++ tailWord_1809832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809832).length < 2 ^ (prefixWord ++ tailWord_1809832).sum := by decide
  have hdescent : baseEnd_1809832 < baseStart_1809832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809847 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 5, 4]
def baseStart_1809847 : Nat := 118140960795 + 1809847 * 2 ^ 59
def prefixEnd_1809847 : Nat := 4983230072969 + 3 ^ 40 * 1809847 * 2
def baseEnd_1809847 : Nat := 309773807365961899663057

theorem tailTrace_1809847 : CollatzResearch.WordTrace tailWord_1809847 prefixEnd_1809847 309773807365961899663057 := by
  unfold tailWord_1809847
  simp only [CollatzResearch.WordTrace]
  refine ⟨66010543074240891104219795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44007028716160594069479863 66010543074240891104219795)
  ·
    refine ⟨99015814611361336656329693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66010543074240891104219795 99015814611361336656329693)
    ·
      refine ⟨37130930479260501246123635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99015814611361336656329693 37130930479260501246123635)
      ·
        refine ⟨55696395718890751869185453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37130930479260501246123635 55696395718890751869185453)
        ·
          refine ⟨20886148394584031950944545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55696395718890751869185453 20886148394584031950944545)
          ·
            refine ⟨15664611295938023963208409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20886148394584031950944545 15664611295938023963208409)
            ·
              refine ⟨11748458471953517972406307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15664611295938023963208409 11748458471953517972406307)
              ·
                refine ⟨17622687707930276958609461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11748458471953517972406307 17622687707930276958609461)
                ·
                  refine ⟨1652126972618463464869637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17622687707930276958609461 1652126972618463464869637)
                  ·
                    refine ⟨309773807365961899663057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1652126972618463464869637 309773807365961899663057)
                    ·
                      rfl

theorem cell23_1809847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_1809847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809847 prefixEnd_1809847 := by exact prefixLift 1809847
  have htrace : WordTrace (prefixWord ++ tailWord_1809847) baseStart_1809847 baseEnd_1809847 := by
    simpa [prefixWord, tailWord_1809847, baseEnd_1809847] using wordTrace_append hprefix tailTrace_1809847
  have hstable : (prefixWord ++ tailWord_1809847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809847).length < 2 ^ (prefixWord ++ tailWord_1809847).sum := by decide
  have hdescent : baseEnd_1809847 < baseStart_1809847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809850 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1809850 : Nat := 118140960795 + 1809850 * 2 ^ 59
def prefixEnd_1809850 : Nat := 4983230072969 + 3 ^ 40 * 1809850 * 2
def baseEnd_1809850 : Nat := 929322962539849187251657

theorem tailTrace_1809850 : CollatzResearch.WordTrace tailWord_1809850 prefixEnd_1809850 929322962539849187251657 := by
  unfold tailWord_1809850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16502663123307505654144751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44007101662153348411052669 16502663123307505654144751)
  ·
    refine ⟨24753994684961258481217127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16502663123307505654144751 24753994684961258481217127)
    ·
      refine ⟨37130992027441887721825691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24753994684961258481217127 37130992027441887721825691)
      ·
        refine ⟨55696488041162831582738537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37130992027441887721825691 55696488041162831582738537)
        ·
          refine ⟨41772366030872123687053903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55696488041162831582738537 41772366030872123687053903)
          ·
            refine ⟨62658549046308185530580855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41772366030872123687053903 62658549046308185530580855)
            ·
              refine ⟨93987823569462278295871283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62658549046308185530580855 93987823569462278295871283)
              ·
                refine ⟨140981735354193417443806925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93987823569462278295871283 140981735354193417443806925)
                ·
                  refine ⟨52868150757822531541427597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140981735354193417443806925 52868150757822531541427597)
                  ·
                    refine ⟨19825556534183449328035349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52868150757822531541427597 19825556534183449328035349)
                    ·
                      refine ⟨929322962539849187251657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19825556534183449328035349 929322962539849187251657)
                      ·
                        rfl

theorem cell23_1809850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1809850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809850 prefixEnd_1809850 := by exact prefixLift 1809850
  have htrace : WordTrace (prefixWord ++ tailWord_1809850) baseStart_1809850 baseEnd_1809850 := by
    simpa [prefixWord, tailWord_1809850, baseEnd_1809850] using wordTrace_append hprefix tailTrace_1809850
  have hstable : (prefixWord ++ tailWord_1809850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809850).length < 2 ^ (prefixWord ++ tailWord_1809850).sum := by decide
  have hdescent : baseEnd_1809850 < baseStart_1809850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809854 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_1809854 : Nat := 118140960795 + 1809854 * 2 ^ 59
def prefixEnd_1809854 : Nat := 4983230072969 + 3 ^ 40 * 1809854 * 2
def baseEnd_1809854 : Nat := 929325016462467171601639

theorem tailTrace_1809854 : CollatzResearch.WordTrace tailWord_1809854 prefixEnd_1809854 929325016462467171601639 := by
  unfold tailWord_1809854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251349798151941412465577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44007198923477020866483077 8251349798151941412465577)
  ·
    refine ⟨6188512348613956059349183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8251349798151941412465577 6188512348613956059349183)
    ·
      refine ⟨9282768522920934089023775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6188512348613956059349183 9282768522920934089023775)
      ·
        refine ⟨13924152784381401133535663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9282768522920934089023775 13924152784381401133535663)
        ·
          refine ⟨20886229176572101700303495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13924152784381401133535663 20886229176572101700303495)
          ·
            refine ⟨31329343764858152550455243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20886229176572101700303495 31329343764858152550455243)
            ·
              refine ⟨46994015647287228825682865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31329343764858152550455243 46994015647287228825682865)
              ·
                refine ⟨35245511735465421619262149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46994015647287228825682865 35245511735465421619262149)
                ·
                  refine ⟨6608533450399766553611653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35245511735465421619262149 6608533450399766553611653)
                  ·
                    refine ⟨1239100021949956228802185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6608533450399766553611653 1239100021949956228802185)
                    ·
                      refine ⟨929325016462467171601639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239100021949956228802185 929325016462467171601639)
                      ·
                        rfl

theorem cell23_1809854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_1809854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809854 prefixEnd_1809854 := by exact prefixLift 1809854
  have htrace : WordTrace (prefixWord ++ tailWord_1809854) baseStart_1809854 baseEnd_1809854 := by
    simpa [prefixWord, tailWord_1809854, baseEnd_1809854] using wordTrace_append hprefix tailTrace_1809854
  have hstable : (prefixWord ++ tailWord_1809854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809854).length < 2 ^ (prefixWord ++ tailWord_1809854).sum := by decide
  have hdescent : baseEnd_1809854 < baseStart_1809854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809881 : List Nat := [1, 2, 1, 2, 4, 3, 1, 4, 1, 4]
def baseStart_1809881 : Nat := 118140960795 + 1809881 * 2 ^ 59
def prefixEnd_1809881 : Nat := 4983230072969 + 3 ^ 40 * 1809881 * 2
def baseEnd_1809881 : Nat := 309779626813379521988005

theorem tailTrace_1809881 : CollatzResearch.WordTrace tailWord_1809881 prefixEnd_1809881 309779626813379521988005 := by
  unfold tailWord_1809881
  simp only [CollatzResearch.WordTrace]
  refine ⟨66011783156117714910957497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44007855437411809940638331 66011783156117714910957497)
  ·
    refine ⟨49508837367088286183218123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66011783156117714910957497 49508837367088286183218123)
    ·
      refine ⟨74263256050632429274827185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49508837367088286183218123 74263256050632429274827185)
      ·
        refine ⟨55697442037974321956120389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74263256050632429274827185 55697442037974321956120389)
        ·
          refine ⟨10443270382120185366772573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55697442037974321956120389 10443270382120185366772573)
          ·
            refine ⟨3916226393295069512539715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10443270382120185366772573 3916226393295069512539715)
            ·
              refine ⟨5874339589942604268809573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916226393295069512539715 5874339589942604268809573)
              ·
                refine ⟨1101438673114238300401795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5874339589942604268809573 1101438673114238300401795)
                ·
                  refine ⟨1652158009671357450602693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101438673114238300401795 1652158009671357450602693)
                  ·
                    refine ⟨309779626813379521988005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1652158009671357450602693 309779626813379521988005)
                    ·
                      rfl

theorem cell23_1809881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 4].length) (baseStart_1809881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809881 prefixEnd_1809881 := by exact prefixLift 1809881
  have htrace : WordTrace (prefixWord ++ tailWord_1809881) baseStart_1809881 baseEnd_1809881 := by
    simpa [prefixWord, tailWord_1809881, baseEnd_1809881] using wordTrace_append hprefix tailTrace_1809881
  have hstable : (prefixWord ++ tailWord_1809881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809881).length < 2 ^ (prefixWord ++ tailWord_1809881).sum := by decide
  have hdescent : baseEnd_1809881 < baseStart_1809881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809904 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 5, 1, 3]
def baseStart_1809904 : Nat := 118140960795 + 1809904 * 2 ^ 59
def prefixEnd_1809904 : Nat := 4983230072969 + 3 ^ 40 * 1809904 * 2
def baseEnd_1809904 : Nat := 929350690495191975976409

theorem tailTrace_1809904 : CollatzResearch.WordTrace tailWord_1809904 prefixEnd_1809904 929350690495191975976409 := by
  unfold tailWord_1809904
  simp only [CollatzResearch.WordTrace]
  refine ⟨33006311017517194919522383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44008414690022926559363177 33006311017517194919522383)
  ·
    refine ⟨49509466526275792379283575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33006311017517194919522383 49509466526275792379283575)
    ·
      refine ⟨74264199789413688568925363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49509466526275792379283575 74264199789413688568925363)
      ·
        refine ⟨111396299684120532853388045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74264199789413688568925363 111396299684120532853388045)
        ·
          refine ⟨41773612381545199820020517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111396299684120532853388045 41773612381545199820020517)
          ·
            refine ⟨7832552321539724966253847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41773612381545199820020517 7832552321539724966253847)
            ·
              refine ⟨11748828482309587449380771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7832552321539724966253847 11748828482309587449380771)
              ·
                refine ⟨17623242723464381174071157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11748828482309587449380771 17623242723464381174071157)
                ·
                  refine ⟨1652179005324785735069171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17623242723464381174071157 1652179005324785735069171)
                  ·
                    refine ⟨2478268507987178602603757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1652179005324785735069171 2478268507987178602603757)
                    ·
                      refine ⟨929350690495191975976409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2478268507987178602603757 929350690495191975976409)
                      ·
                        rfl

theorem cell23_1809904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 1, 3].length) (baseStart_1809904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809904 prefixEnd_1809904 := by exact prefixLift 1809904
  have htrace : WordTrace (prefixWord ++ tailWord_1809904) baseStart_1809904 baseEnd_1809904 := by
    simpa [prefixWord, tailWord_1809904, baseEnd_1809904] using wordTrace_append hprefix tailTrace_1809904
  have hstable : (prefixWord ++ tailWord_1809904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809904).length < 2 ^ (prefixWord ++ tailWord_1809904).sum := by decide
  have hdescent : baseEnd_1809904 < baseStart_1809904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809914 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2]
def baseStart_1809914 : Nat := 118140960795 + 1809914 * 2 ^ 59
def prefixEnd_1809914 : Nat := 4983230072969 + 3 ^ 40 * 1809914 * 2
def baseEnd_1809914 : Nat := 929355825301736936851363

theorem tailTrace_1809914 : CollatzResearch.WordTrace tailWord_1809914 prefixEnd_1809914 929355825301736936851363 := by
  unfold tailWord_1809914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16503246691249540386727199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44008657843332107697939197 16503246691249540386727199)
  ·
    refine ⟨24754870036874310580090799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16503246691249540386727199 24754870036874310580090799)
    ·
      refine ⟨37132305055311465870136199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24754870036874310580090799 37132305055311465870136199)
      ·
        refine ⟨55698457582967198805204299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37132305055311465870136199 55698457582967198805204299)
        ·
          refine ⟨83547686374450798207806449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55698457582967198805204299 83547686374450798207806449)
          ·
            refine ⟨62660764780838098655854837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83547686374450798207806449 62660764780838098655854837)
            ·
              refine ⟨5874446698203571748986391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62660764780838098655854837 5874446698203571748986391)
              ·
                refine ⟨8811670047305357623479587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874446698203571748986391 8811670047305357623479587)
                ·
                  refine ⟨13217505070958036435219381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8811670047305357623479587 13217505070958036435219381)
                  ·
                    refine ⟨1239141100402315915801817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13217505070958036435219381 1239141100402315915801817)
                    ·
                      refine ⟨929355825301736936851363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239141100402315915801817 929355825301736936851363)
                      ·
                        rfl

theorem cell23_1809914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_1809914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809914 prefixEnd_1809914 := by exact prefixLift 1809914
  have htrace : WordTrace (prefixWord ++ tailWord_1809914) baseStart_1809914 baseEnd_1809914 := by
    simpa [prefixWord, tailWord_1809914, baseEnd_1809914] using wordTrace_append hprefix tailTrace_1809914
  have hstable : (prefixWord ++ tailWord_1809914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809914).length < 2 ^ (prefixWord ++ tailWord_1809914).sum := by decide
  have hdescent : baseEnd_1809914 < baseStart_1809914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809954 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_1809954 : Nat := 118140960795 + 1809954 * 2 ^ 59
def prefixEnd_1809954 : Nat := 4983230072969 + 3 ^ 40 * 1809954 * 2
def baseEnd_1809954 : Nat := 309792121509305593450393

theorem tailTrace_1809954 : CollatzResearch.WordTrace tailWord_1809954 prefixEnd_1809954 309792121509305593450393 := by
  unfold tailWord_1809954
  simp only [CollatzResearch.WordTrace]
  refine ⟨16503611421213312094591229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44009630456568832252243277 16503611421213312094591229)
  ·
    refine ⟨6188854282954992035471711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16503611421213312094591229 6188854282954992035471711)
    ·
      refine ⟨9283281424432488053207567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6188854282954992035471711 9283281424432488053207567)
      ·
        refine ⟨13924922136648732079811351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9283281424432488053207567 13924922136648732079811351)
        ·
          refine ⟨20887383204973098119717027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13924922136648732079811351 20887383204973098119717027)
          ·
            refine ⟨31331074807459647179575541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20887383204973098119717027 31331074807459647179575541)
            ·
              refine ⟨2937288263199341923085207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31331074807459647179575541 2937288263199341923085207)
              ·
                refine ⟨4405932394799012884627811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937288263199341923085207 4405932394799012884627811)
                ·
                  refine ⟨6608898592198519326941717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405932394799012884627811 6608898592198519326941717)
                  ·
                    refine ⟨309792121509305593450393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6608898592198519326941717 309792121509305593450393)
                    ·
                      rfl

theorem cell23_1809954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_1809954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809954 prefixEnd_1809954 := by exact prefixLift 1809954
  have htrace : WordTrace (prefixWord ++ tailWord_1809954) baseStart_1809954 baseEnd_1809954 := by
    simpa [prefixWord, tailWord_1809954, baseEnd_1809954] using wordTrace_append hprefix tailTrace_1809954
  have hstable : (prefixWord ++ tailWord_1809954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809954).length < 2 ^ (prefixWord ++ tailWord_1809954).sum := by decide
  have hdescent : baseEnd_1809954 < baseStart_1809954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1809981 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1809981 : Nat := 118140960795 + 1809981 * 2 ^ 59
def prefixEnd_1809981 : Nat := 4983230072969 + 3 ^ 40 * 1809981 * 2
def baseEnd_1809981 : Nat := 929390228505588174713555

theorem tailTrace_1809981 : CollatzResearch.WordTrace tailWord_1809981 prefixEnd_1809981 929390228505588174713555 := by
  unfold tailWord_1809981
  simp only [CollatzResearch.WordTrace]
  refine ⟨66015430455755431989597797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44010286970503621326398531 66015430455755431989597797)
  ·
    refine ⟨12377893210454143498049587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66015430455755431989597797 12377893210454143498049587)
    ·
      refine ⟨18566839815681215247074381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12377893210454143498049587 18566839815681215247074381)
      ·
        refine ⟨6962564930880455717652893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18566839815681215247074381 6962564930880455717652893)
        ·
          refine ⟨2610961849080170894119835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6962564930880455717652893 2610961849080170894119835)
          ·
            refine ⟨3916442773620256341179753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610961849080170894119835 3916442773620256341179753)
            ·
              refine ⟨2937332080215192255884815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3916442773620256341179753 2937332080215192255884815)
              ·
                refine ⟨4405998120322788383827223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937332080215192255884815 4405998120322788383827223)
                ·
                  refine ⟨6608997180484182575740835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405998120322788383827223 6608997180484182575740835)
                  ·
                    refine ⟨9913495770726273863611253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6608997180484182575740835 9913495770726273863611253)
                    ·
                      refine ⟨929390228505588174713555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9913495770726273863611253 929390228505588174713555)
                      ·
                        rfl

theorem cell23_1809981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1809981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1809981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1809981 prefixEnd_1809981 := by exact prefixLift 1809981
  have htrace : WordTrace (prefixWord ++ tailWord_1809981) baseStart_1809981 baseEnd_1809981 := by
    simpa [prefixWord, tailWord_1809981, baseEnd_1809981] using wordTrace_append hprefix tailTrace_1809981
  have hstable : (prefixWord ++ tailWord_1809981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1809981).length < 2 ^ (prefixWord ++ tailWord_1809981).sum := by decide
  have hdescent : baseEnd_1809981 < baseStart_1809981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1809981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810102 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_1810102 : Nat := 118140960795 + 1810102 * 2 ^ 59
def prefixEnd_1810102 : Nat := 4983230072969 + 3 ^ 40 * 1810102 * 2
def baseEnd_1810102 : Nat := 929452359664782201300499

theorem tailTrace_1810102 : CollatzResearch.WordTrace tailWord_1810102 prefixEnd_1810102 929452359664782201300499 := by
  unfold tailWord_1810102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126240230519816853422035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44013229125544713103168373 4126240230519816853422035)
  ·
    refine ⟨6189360345779725280133053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4126240230519816853422035 6189360345779725280133053)
    ·
      refine ⟨2321010129667396980049895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6189360345779725280133053 2321010129667396980049895)
      ·
        refine ⟨3481515194501095470074843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2321010129667396980049895 3481515194501095470074843)
        ·
          refine ⟨5222272791751643205112265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3481515194501095470074843 5222272791751643205112265)
          ·
            refine ⟨3916704593813732403834199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5222272791751643205112265 3916704593813732403834199)
            ·
              refine ⟨5875056890720598605751299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916704593813732403834199 5875056890720598605751299)
              ·
                refine ⟨8812585336080897908626949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5875056890720598605751299 8812585336080897908626949)
                ·
                  refine ⟨1652359750515168357867553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8812585336080897908626949 1652359750515168357867553)
                  ·
                    refine ⟨1239269812886376268400665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1652359750515168357867553 1239269812886376268400665)
                    ·
                      refine ⟨929452359664782201300499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239269812886376268400665 929452359664782201300499)
                      ·
                        rfl

theorem cell23_1810102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_1810102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810102 prefixEnd_1810102 := by exact prefixLift 1810102
  have htrace : WordTrace (prefixWord ++ tailWord_1810102) baseStart_1810102 baseEnd_1810102 := by
    simpa [prefixWord, tailWord_1810102, baseEnd_1810102] using wordTrace_append hprefix tailTrace_1810102
  have hstable : (prefixWord ++ tailWord_1810102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810102).length < 2 ^ (prefixWord ++ tailWord_1810102).sum := by decide
  have hdescent : baseEnd_1810102 < baseStart_1810102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810104 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 2, 5]
def baseStart_1810104 : Nat := 118140960795 + 1810104 * 2 ^ 59
def prefixEnd_1810104 : Nat := 4983230072969 + 3 ^ 40 * 1810104 * 2
def baseEnd_1810104 : Nat := 309817795542030397825163

theorem tailTrace_1810104 : CollatzResearch.WordTrace tailWord_1810104 prefixEnd_1810104 309817795542030397825163 := by
  unfold tailWord_1810104
  simp only [CollatzResearch.WordTrace]
  refine ⟨33009958317154911998162683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44013277756206549330883577 33009958317154911998162683)
  ·
    refine ⟨49514937475732367997244025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33009958317154911998162683 49514937475732367997244025)
    ·
      refine ⟨37136203106799275997933019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49514937475732367997244025 37136203106799275997933019)
      ·
        refine ⟨55704304660198913996899529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37136203106799275997933019 55704304660198913996899529)
        ·
          refine ⟨41778228495149185497674647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55704304660198913996899529 41778228495149185497674647)
          ·
            refine ⟨62667342742723778246511971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41778228495149185497674647 62667342742723778246511971)
            ·
              refine ⟨94001014114085667369767957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62667342742723778246511971 94001014114085667369767957)
              ·
                refine ⟨4406297536597765657957873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94001014114085667369767957 4406297536597765657957873)
                ·
                  refine ⟨3304723152448324243468405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4406297536597765657957873 3304723152448324243468405)
                  ·
                    refine ⟨309817795542030397825163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3304723152448324243468405 309817795542030397825163)
                    ·
                      rfl

theorem cell23_1810104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_1810104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810104 prefixEnd_1810104 := by exact prefixLift 1810104
  have htrace : WordTrace (prefixWord ++ tailWord_1810104) baseStart_1810104 baseEnd_1810104 := by
    simpa [prefixWord, tailWord_1810104, baseEnd_1810104] using wordTrace_append hprefix tailTrace_1810104
  have hstable : (prefixWord ++ tailWord_1810104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810104).length < 2 ^ (prefixWord ++ tailWord_1810104).sum := by decide
  have hdescent : baseEnd_1810104 < baseStart_1810104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810154 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1810154 : Nat := 118140960795 + 1810154 * 2 ^ 59
def prefixEnd_1810154 : Nat := 4983230072969 + 3 ^ 40 * 1810154 * 2
def baseEnd_1810154 : Nat := 929479060658815997850259

theorem tailTrace_1810154 : CollatzResearch.WordTrace tailWord_1810154 prefixEnd_1810154 929479060658815997850259 := by
  unfold tailWord_1810154
  simp only [CollatzResearch.WordTrace]
  refine ⟨16505435071032170633911379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44014493522752455023763677 16505435071032170633911379)
  ·
    refine ⟨24758152606548255950867069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16505435071032170633911379 24758152606548255950867069)
    ·
      refine ⟨9284307227455595981575151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24758152606548255950867069 9284307227455595981575151)
      ·
        refine ⟨13926460841183393972362727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9284307227455595981575151 13926460841183393972362727)
        ·
          refine ⟨20889691261775090958544091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13926460841183393972362727 20889691261775090958544091)
          ·
            refine ⟨31334536892662636437816137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20889691261775090958544091 31334536892662636437816137)
            ·
              refine ⟨23500902669496977328362103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31334536892662636437816137 23500902669496977328362103)
              ·
                refine ⟨35251354004245465992543155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23500902669496977328362103 35251354004245465992543155)
                ·
                  refine ⟨52877031006368198988814733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35251354004245465992543155 52877031006368198988814733)
                  ·
                    refine ⟨19828886627388074620805525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52877031006368198988814733 19828886627388074620805525)
                    ·
                      refine ⟨929479060658815997850259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19828886627388074620805525 929479060658815997850259)
                      ·
                        rfl

theorem cell23_1810154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1810154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810154 prefixEnd_1810154 := by exact prefixLift 1810154
  have htrace : WordTrace (prefixWord ++ tailWord_1810154) baseStart_1810154 baseEnd_1810154 := by
    simpa [prefixWord, tailWord_1810154, baseEnd_1810154] using wordTrace_append hprefix tailTrace_1810154
  have hstable : (prefixWord ++ tailWord_1810154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810154).length < 2 ^ (prefixWord ++ tailWord_1810154).sum := by decide
  have hdescent : baseEnd_1810154 < baseStart_1810154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810161 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_1810161 : Nat := 118140960795 + 1810161 * 2 ^ 59
def prefixEnd_1810161 : Nat := 4983230072969 + 3 ^ 40 * 1810161 * 2
def baseEnd_1810161 : Nat := 929482655023397470462727

theorem tailTrace_1810161 : CollatzResearch.WordTrace tailWord_1810161 prefixEnd_1810161 929482655023397470462727 := by
  unfold tailWord_1810161
  simp only [CollatzResearch.WordTrace]
  refine ⟨66021995595103322731150337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44014663730068881820766891 66021995595103322731150337)
  ·
    refine ⟨49516496696327492048362753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66021995595103322731150337 49516496696327492048362753)
    ·
      refine ⟨37137372522245619036272065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49516496696327492048362753 37137372522245619036272065)
      ·
        refine ⟨27853029391684214277204049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37137372522245619036272065 27853029391684214277204049)
        ·
          refine ⟨20889772043763160707903037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27853029391684214277204049 20889772043763160707903037)
          ·
            refine ⟨7833664516411185265463639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20889772043763160707903037 7833664516411185265463639)
            ·
              refine ⟨11750496774616777898195459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833664516411185265463639 11750496774616777898195459)
              ·
                refine ⟨17625745161925166847293189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11750496774616777898195459 17625745161925166847293189)
                ·
                  refine ⟨3304827217860968783867473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17625745161925166847293189 3304827217860968783867473)
                  ·
                    refine ⟨2478620413395726587900605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3304827217860968783867473 2478620413395726587900605)
                    ·
                      refine ⟨929482655023397470462727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2478620413395726587900605 929482655023397470462727)
                      ·
                        rfl

theorem cell23_1810161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_1810161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810161 prefixEnd_1810161 := by exact prefixLift 1810161
  have htrace : WordTrace (prefixWord ++ tailWord_1810161) baseStart_1810161 baseEnd_1810161 := by
    simpa [prefixWord, tailWord_1810161, baseEnd_1810161] using wordTrace_append hprefix tailTrace_1810161
  have hstable : (prefixWord ++ tailWord_1810161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810161).length < 2 ^ (prefixWord ++ tailWord_1810161).sum := by decide
  have hdescent : baseEnd_1810161 < baseStart_1810161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810178 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1810178 : Nat := 118140960795 + 1810178 * 2 ^ 59
def prefixEnd_1810178 : Nat := 4983230072969 + 3 ^ 40 * 1810178 * 2
def baseEnd_1810178 : Nat := 929491384194523903950149

theorem tailTrace_1810178 : CollatzResearch.WordTrace tailWord_1810178 prefixEnd_1810178 929491384194523903950149 := by
  unfold tailWord_1810178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16505653909010433658629797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44015077090694489756346125 16505653909010433658629797)
  ·
    refine ⟨3094810107939456310993087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16505653909010433658629797 3094810107939456310993087)
    ·
      refine ⟨4642215161909184466489631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094810107939456310993087 4642215161909184466489631)
      ·
        refine ⟨6963322742863776699734447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642215161909184466489631 6963322742863776699734447)
        ·
          refine ⟨10444984114295665049601671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6963322742863776699734447 10444984114295665049601671)
          ·
            refine ⟨15667476171443497574402507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444984114295665049601671 15667476171443497574402507)
            ·
              refine ⟨23501214257165246361603761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15667476171443497574402507 23501214257165246361603761)
              ·
                refine ⟨17625910692873934771202821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23501214257165246361603761 17625910692873934771202821)
                ·
                  refine ⟨3304858254913862769600529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17625910692873934771202821 3304858254913862769600529)
                  ·
                    refine ⟨2478643691185397077200397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3304858254913862769600529 2478643691185397077200397)
                    ·
                      refine ⟨929491384194523903950149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2478643691185397077200397 929491384194523903950149)
                      ·
                        rfl

theorem cell23_1810178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1810178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810178 prefixEnd_1810178 := by exact prefixLift 1810178
  have htrace : WordTrace (prefixWord ++ tailWord_1810178) baseStart_1810178 baseEnd_1810178 := by
    simpa [prefixWord, tailWord_1810178, baseEnd_1810178] using wordTrace_append hprefix tailTrace_1810178
  have hstable : (prefixWord ++ tailWord_1810178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810178).length < 2 ^ (prefixWord ++ tailWord_1810178).sum := by decide
  have hdescent : baseEnd_1810178 < baseStart_1810178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810189 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1810189 : Nat := 118140960795 + 1810189 * 2 ^ 59
def prefixEnd_1810189 : Nat := 4983230072969 + 3 ^ 40 * 1810189 * 2
def baseEnd_1810189 : Nat := 309832344160574453637533

theorem tailTrace_1810189 : CollatzResearch.WordTrace tailWord_1810189 prefixEnd_1810189 309832344160574453637533 := by
  unfold tailWord_1810189
  simp only [CollatzResearch.WordTrace]
  refine ⟨66023016839001883513169621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44015344559334589008779747 66023016839001883513169621)
  ·
    refine ⟨1547414457164106644839913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 66023016839001883513169621 1547414457164106644839913)
    ·
      refine ⟨1160560842873079983629935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1547414457164106644839913 1160560842873079983629935)
      ·
        refine ⟨1740841264309619975444903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160560842873079983629935 1740841264309619975444903)
        ·
          refine ⟨2611261896464429963167355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740841264309619975444903 2611261896464429963167355)
          ·
            refine ⟨3916892844696644944751033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611261896464429963167355 3916892844696644944751033)
            ·
              refine ⟨2937669633522483708563275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3916892844696644944751033 2937669633522483708563275)
              ·
                refine ⟨4406504450283725562844913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937669633522483708563275 4406504450283725562844913)
                ·
                  refine ⟨3304878337712794172133685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4406504450283725562844913 3304878337712794172133685)
                  ·
                    refine ⟨309832344160574453637533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3304878337712794172133685 309832344160574453637533)
                    ·
                      rfl

theorem cell23_1810189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1810189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810189 prefixEnd_1810189 := by exact prefixLift 1810189
  have htrace : WordTrace (prefixWord ++ tailWord_1810189) baseStart_1810189 baseEnd_1810189 := by
    simpa [prefixWord, tailWord_1810189, baseEnd_1810189] using wordTrace_append hprefix tailTrace_1810189
  have hstable : (prefixWord ++ tailWord_1810189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810189).length < 2 ^ (prefixWord ++ tailWord_1810189).sum := by decide
  have hdescent : baseEnd_1810189 < baseStart_1810189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810201 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 5, 5, 2]
def baseStart_1810201 : Nat := 118140960795 + 1810201 * 2 ^ 59
def prefixEnd_1810201 : Nat := 4983230072969 + 3 ^ 40 * 1810201 * 2
def baseEnd_1810201 : Nat := 929503194249577313962543

theorem tailTrace_1810201 : CollatzResearch.WordTrace tailWord_1810201 prefixEnd_1810201 929503194249577313962543 := by
  unfold tailWord_1810201
  simp only [CollatzResearch.WordTrace]
  refine ⟨66023454514958409562606457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44015636343305606375070971 66023454514958409562606457)
  ·
    refine ⟨49517590886218807171954843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66023454514958409562606457 49517590886218807171954843)
    ·
      refine ⟨74276386329328210757932265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49517590886218807171954843 74276386329328210757932265)
      ·
        refine ⟨55707289746996158068449199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74276386329328210757932265 55707289746996158068449199)
        ·
          refine ⟨83560934620494237102673799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55707289746996158068449199 83560934620494237102673799)
          ·
            refine ⟨125341401930741355654010699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83560934620494237102673799 125341401930741355654010699)
            ·
              refine ⟨188012102896112033481016049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125341401930741355654010699 188012102896112033481016049)
              ·
                refine ⟨141009077172084025110762037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188012102896112033481016049 141009077172084025110762037)
                ·
                  refine ⟨13219600984882877354133941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141009077172084025110762037 13219600984882877354133941)
                  ·
                    refine ⟨1239337592332769751950057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13219600984882877354133941 1239337592332769751950057)
                    ·
                      refine ⟨929503194249577313962543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239337592332769751950057 929503194249577313962543)
                      ·
                        rfl

theorem cell23_1810201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_1810201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810201 prefixEnd_1810201 := by exact prefixLift 1810201
  have htrace : WordTrace (prefixWord ++ tailWord_1810201) baseStart_1810201 baseEnd_1810201 := by
    simpa [prefixWord, tailWord_1810201, baseEnd_1810201] using wordTrace_append hprefix tailTrace_1810201
  have hstable : (prefixWord ++ tailWord_1810201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810201).length < 2 ^ (prefixWord ++ tailWord_1810201).sum := by decide
  have hdescent : baseEnd_1810201 < baseStart_1810201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810211 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 1, 5]
def baseStart_1810211 : Nat := 118140960795 + 1810211 * 2 ^ 59
def prefixEnd_1810211 : Nat := 4983230072969 + 3 ^ 40 * 1810211 * 2
def baseEnd_1810211 : Nat := 309836109685374091612499

theorem tailTrace_1810211 : CollatzResearch.WordTrace tailWord_1810211 prefixEnd_1810211 309836109685374091612499 := by
  unfold tailWord_1810211
  simp only [CollatzResearch.WordTrace]
  refine ⟨66023819244922181270470487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44015879496614787513646991 66023819244922181270470487)
  ·
    refine ⟨99035728867383271905705731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66023819244922181270470487 99035728867383271905705731)
    ·
      refine ⟨148553593301074907858558597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99035728867383271905705731 148553593301074907858558597)
      ·
        refine ⟨27853798743951545223479737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148553593301074907858558597 27853798743951545223479737)
        ·
          refine ⟨20890349057963658917609803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27853798743951545223479737 20890349057963658917609803)
          ·
            refine ⟨31335523586945488376414705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20890349057963658917609803 31335523586945488376414705)
            ·
              refine ⟨23501642690209116282311029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31335523586945488376414705 23501642690209116282311029)
              ·
                refine ⟨2203279002207104651466659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23501642690209116282311029 2203279002207104651466659)
                ·
                  refine ⟨3304918503310656977199989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203279002207104651466659 3304918503310656977199989)
                  ·
                    refine ⟨309836109685374091612499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3304918503310656977199989 309836109685374091612499)
                    ·
                      rfl

theorem cell23_1810211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 5].length) (baseStart_1810211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810211 prefixEnd_1810211 := by exact prefixLift 1810211
  have htrace : WordTrace (prefixWord ++ tailWord_1810211) baseStart_1810211 baseEnd_1810211 := by
    simpa [prefixWord, tailWord_1810211, baseEnd_1810211] using wordTrace_append hprefix tailTrace_1810211
  have hstable : (prefixWord ++ tailWord_1810211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810211).length < 2 ^ (prefixWord ++ tailWord_1810211).sum := by decide
  have hdescent : baseEnd_1810211 < baseStart_1810211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810228 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1810228 : Nat := 118140960795 + 1810228 * 2 ^ 59
def prefixEnd_1810228 : Nat := 4983230072969 + 3 ^ 40 * 1810228 * 2
def baseEnd_1810228 : Nat := 309839019409082902774973

theorem tailTrace_1810228 : CollatzResearch.WordTrace tailWord_1810228 prefixEnd_1810228 309839019409082902774973 := by
  unfold tailWord_1810228
  simp only [CollatzResearch.WordTrace]
  refine ⟨33012219642930296586919669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44016292857240395449226225 33012219642930296586919669)
  ·
    refine ⟨3094895591524715305023719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33012219642930296586919669 3094895591524715305023719)
    ·
      refine ⟨4642343387287072957535579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094895591524715305023719 4642343387287072957535579)
      ·
        refine ⟨6963515080930609436303369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642343387287072957535579 6963515080930609436303369)
        ·
          refine ⟨5222636310697957077227527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6963515080930609436303369 5222636310697957077227527)
          ·
            refine ⟨7833954466046935615841291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5222636310697957077227527 7833954466046935615841291)
            ·
              refine ⟨11750931699070403423761937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833954466046935615841291 11750931699070403423761937)
              ·
                refine ⟨8813198774302802567821453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11750931699070403423761937 8813198774302802567821453)
                ·
                  refine ⟨3304949540363550962933045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8813198774302802567821453 3304949540363550962933045)
                  ·
                    refine ⟨309839019409082902774973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3304949540363550962933045 309839019409082902774973)
                    ·
                      rfl

theorem cell23_1810228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1810228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810228 prefixEnd_1810228 := by exact prefixLift 1810228
  have htrace : WordTrace (prefixWord ++ tailWord_1810228) baseStart_1810228 baseEnd_1810228 := by
    simpa [prefixWord, tailWord_1810228, baseEnd_1810228] using wordTrace_append hprefix tailTrace_1810228
  have hstable : (prefixWord ++ tailWord_1810228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810228).length < 2 ^ (prefixWord ++ tailWord_1810228).sum := by decide
  have hdescent : baseEnd_1810228 < baseStart_1810228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810252 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 2, 3, 2]
def baseStart_1810252 : Nat := 118140960795 + 1810252 * 2 ^ 59
def prefixEnd_1810252 : Nat := 4983230072969 + 3 ^ 40 * 1810252 * 2
def baseEnd_1810252 : Nat := 929529381762956614424809

theorem tailTrace_1810252 : CollatzResearch.WordTrace tailWord_1810252 prefixEnd_1810252 929529381762956614424809 := by
  unfold tailWord_1810252
  simp only [CollatzResearch.WordTrace]
  refine ⟨33012657318886822636356505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44016876425182430181808673 33012657318886822636356505)
  ·
    refine ⟨24759492989165116977267379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33012657318886822636356505 24759492989165116977267379)
    ·
      refine ⟨37139239483747675465901069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24759492989165116977267379 37139239483747675465901069)
      ·
        refine ⟨13927214806405378299712901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37139239483747675465901069 13927214806405378299712901)
        ·
          refine ⟨2611352776201008431196169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13927214806405378299712901 2611352776201008431196169)
          ·
            refine ⟨1958514582150756323397127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611352776201008431196169 1958514582150756323397127)
            ·
              refine ⟨2937771873226134485095691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958514582150756323397127 2937771873226134485095691)
              ·
                refine ⟨4406657809839201727643537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937771873226134485095691 4406657809839201727643537)
                ·
                  refine ⟨3304993357379401295732653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4406657809839201727643537 3304993357379401295732653)
                  ·
                    refine ⟨1239372509017275485899745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3304993357379401295732653 1239372509017275485899745)
                    ·
                      refine ⟨929529381762956614424809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239372509017275485899745 929529381762956614424809)
                      ·
                        rfl

theorem cell23_1810252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_1810252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810252 prefixEnd_1810252 := by exact prefixLift 1810252
  have htrace : WordTrace (prefixWord ++ tailWord_1810252) baseStart_1810252 baseEnd_1810252 := by
    simpa [prefixWord, tailWord_1810252, baseEnd_1810252] using wordTrace_append hprefix tailTrace_1810252
  have hstable : (prefixWord ++ tailWord_1810252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810252).length < 2 ^ (prefixWord ++ tailWord_1810252).sum := by decide
  have hdescent : baseEnd_1810252 < baseStart_1810252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810281 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 3]
def baseStart_1810281 : Nat := 118140960795 + 1810281 * 2 ^ 59
def prefixEnd_1810281 : Nat := 4983230072969 + 3 ^ 40 * 1810281 * 2
def baseEnd_1810281 : Nat := 929544272701937000962175

theorem tailTrace_1810281 : CollatzResearch.WordTrace tailWord_1810281 prefixEnd_1810281 929544272701937000962175 := by
  unfold tailWord_1810281
  simp only [CollatzResearch.WordTrace]
  refine ⟨66026372354668583225518697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44017581569779055483679131 66026372354668583225518697)
  ·
    refine ⟨49519779266001437419139023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66026372354668583225518697 49519779266001437419139023)
    ·
      refine ⟨74279668899002156128708535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49519779266001437419139023 74279668899002156128708535)
      ·
        refine ⟨111419503348503234193062803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74279668899002156128708535 111419503348503234193062803)
        ·
          refine ⟨167129255022754851289594205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111419503348503234193062803 167129255022754851289594205)
          ·
            refine ⟨62673470633533069233597827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167129255022754851289594205 62673470633533069233597827)
            ·
              refine ⟨94010205950299603850396741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62673470633533069233597827 94010205950299603850396741)
              ·
                refine ⟨17626913615681175721949389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94010205950299603850396741 17626913615681175721949389)
                ·
                  refine ⟨6610092605880440895731021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17626913615681175721949389 6610092605880440895731021)
                  ·
                    refine ⟨2478784727205165335899133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6610092605880440895731021 2478784727205165335899133)
                    ·
                      refine ⟨929544272701937000962175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2478784727205165335899133 929544272701937000962175)
                      ·
                        rfl

theorem cell23_1810281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_1810281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810281 prefixEnd_1810281 := by exact prefixLift 1810281
  have htrace : WordTrace (prefixWord ++ tailWord_1810281) baseStart_1810281 baseEnd_1810281 := by
    simpa [prefixWord, tailWord_1810281, baseEnd_1810281] using wordTrace_append hprefix tailTrace_1810281
  have hstable : (prefixWord ++ tailWord_1810281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810281).length < 2 ^ (prefixWord ++ tailWord_1810281).sum := by decide
  have hdescent : baseEnd_1810281 < baseStart_1810281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810298 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_1810298 : Nat := 118140960795 + 1810298 * 2 ^ 59
def prefixEnd_1810298 : Nat := 4983230072969 + 3 ^ 40 * 1810298 * 2
def baseEnd_1810298 : Nat := 929553001873063434449597

theorem tailTrace_1810298 : CollatzResearch.WordTrace tailWord_1810298 prefixEnd_1810298 929553001873063434449597 := by
  unfold tailWord_1810298
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506748098901748782221887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44017994930404663419258365 16506748098901748782221887)
  ·
    refine ⟨24760122148352623173332831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16506748098901748782221887 24760122148352623173332831)
    ·
      refine ⟨37140183222528934759999247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24760122148352623173332831 37140183222528934759999247)
      ·
        refine ⟨55710274833793402139998871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37140183222528934759999247 55710274833793402139998871)
        ·
          refine ⟨83565412250690103209998307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55710274833793402139998871 83565412250690103209998307)
          ·
            refine ⟨125348118376035154814997461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83565412250690103209998307 125348118376035154814997461)
            ·
              refine ⟨2937846524438323940976503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 125348118376035154814997461 2937846524438323940976503)
              ·
                refine ⟨4406769786657485911464755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937846524438323940976503 4406769786657485911464755)
                ·
                  refine ⟨6610154679986228867197133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406769786657485911464755 6610154679986228867197133)
                  ·
                    refine ⟨2478808004994835825198925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6610154679986228867197133 2478808004994835825198925)
                    ·
                      refine ⟨929553001873063434449597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2478808004994835825198925 929553001873063434449597)
                      ·
                        rfl

theorem cell23_1810298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_1810298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810298 prefixEnd_1810298 := by exact prefixLift 1810298
  have htrace : WordTrace (prefixWord ++ tailWord_1810298) baseStart_1810298 baseEnd_1810298 := by
    simpa [prefixWord, tailWord_1810298, baseEnd_1810298] using wordTrace_append hprefix tailTrace_1810298
  have hstable : (prefixWord ++ tailWord_1810298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810298).length < 2 ^ (prefixWord ++ tailWord_1810298).sum := by decide
  have hdescent : baseEnd_1810298 < baseStart_1810298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810302 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1810302 : Nat := 118140960795 + 1810302 * 2 ^ 59
def prefixEnd_1810302 : Nat := 4983230072969 + 3 ^ 40 * 1810302 * 2
def baseEnd_1810302 : Nat := 929555055795681418799579

theorem tailTrace_1810302 : CollatzResearch.WordTrace tailWord_1810302 prefixEnd_1810302 929555055795681418799579 := by
  unfold tailWord_1810302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8253392285949062976504145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44018092191728335874688773 8253392285949062976504145)
  ·
    refine ⟨6190044214461797232378109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8253392285949062976504145 6190044214461797232378109)
    ·
      refine ⟨2321266580423173962141791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6190044214461797232378109 2321266580423173962141791)
      ·
        refine ⟨3481899870634760943212687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2321266580423173962141791 3481899870634760943212687)
        ·
          refine ⟨5222849805952141414819031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3481899870634760943212687 5222849805952141414819031)
          ·
            refine ⟨7834274708928212122228547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5222849805952141414819031 7834274708928212122228547)
            ·
              refine ⟨11751412063392318183342821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7834274708928212122228547 11751412063392318183342821)
              ·
                refine ⟨2203389761886059659376779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11751412063392318183342821 2203389761886059659376779)
                ·
                  refine ⟨3305084642829089489065169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203389761886059659376779 3305084642829089489065169)
                  ·
                    refine ⟨2478813482121817116798877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3305084642829089489065169 2478813482121817116798877)
                    ·
                      refine ⟨929555055795681418799579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2478813482121817116798877 929555055795681418799579)
                      ·
                        rfl

theorem cell23_1810302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1810302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810302 prefixEnd_1810302 := by exact prefixLift 1810302
  have htrace : WordTrace (prefixWord ++ tailWord_1810302) baseStart_1810302 baseEnd_1810302 := by
    simpa [prefixWord, tailWord_1810302, baseEnd_1810302] using wordTrace_append hprefix tailTrace_1810302
  have hstable : (prefixWord ++ tailWord_1810302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810302).length < 2 ^ (prefixWord ++ tailWord_1810302).sum := by decide
  have hdescent : baseEnd_1810302 < baseStart_1810302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810325 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_1810325 : Nat := 118140960795 + 1810325 * 2 ^ 59
def prefixEnd_1810325 : Nat := 4983230072969 + 3 ^ 40 * 1810325 * 2
def baseEnd_1810325 : Nat := 929566865850734828811973

theorem tailTrace_1810325 : CollatzResearch.WordTrace tailWord_1810325 prefixEnd_1810325 929566865850734828811973 := by
  unfold tailWord_1810325
  simp only [CollatzResearch.WordTrace]
  refine ⟨66027977166509178740120429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44018651444339452493413619 66027977166509178740120429)
  ·
    refine ⟨24760491437440942027545161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66027977166509178740120429 24760491437440942027545161)
    ·
      refine ⟨18570368578080706520658871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24760491437440942027545161 18570368578080706520658871)
      ·
        refine ⟨27855552867121059780988307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18570368578080706520658871 27855552867121059780988307)
        ·
          refine ⟨41783329300681589671482461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27855552867121059780988307 41783329300681589671482461)
          ·
            refine ⟨15668748487755596126805923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41783329300681589671482461 15668748487755596126805923)
            ·
              refine ⟨23503122731633394190208885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15668748487755596126805923 23503122731633394190208885)
              ·
                refine ⟨2203417756090630705332083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23503122731633394190208885 2203417756090630705332083)
                ·
                  refine ⟨3305126634135946057998125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203417756090630705332083 3305126634135946057998125)
                  ·
                    refine ⟨1239422487800979771749297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3305126634135946057998125 1239422487800979771749297)
                    ·
                      refine ⟨929566865850734828811973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239422487800979771749297 929566865850734828811973)
                      ·
                        rfl

theorem cell23_1810325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_1810325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810325 prefixEnd_1810325 := by exact prefixLift 1810325
  have htrace : WordTrace (prefixWord ++ tailWord_1810325) baseStart_1810325 baseEnd_1810325 := by
    simpa [prefixWord, tailWord_1810325, baseEnd_1810325] using wordTrace_append hprefix tailTrace_1810325
  have hstable : (prefixWord ++ tailWord_1810325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810325).length < 2 ^ (prefixWord ++ tailWord_1810325).sum := by decide
  have hdescent : baseEnd_1810325 < baseStart_1810325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810351 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_1810351 : Nat := 118140960795 + 1810351 * 2 ^ 59
def prefixEnd_1810351 : Nat := 4983230072969 + 3 ^ 40 * 1810351 * 2
def baseEnd_1810351 : Nat := 929580216347751727086853

theorem tailTrace_1810351 : CollatzResearch.WordTrace tailWord_1810351 prefixEnd_1810351 929580216347751727086853 := by
  unfold tailWord_1810351
  simp only [CollatzResearch.WordTrace]
  refine ⟨66028925464414985180566907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44019283642943323453711271 66028925464414985180566907)
  ·
    refine ⟨99043388196622477770850361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66028925464414985180566907 99043388196622477770850361)
    ·
      refine ⟨74282541147466858328137771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99043388196622477770850361 74282541147466858328137771)
      ·
        refine ⟨111423811721200287492206657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74282541147466858328137771 111423811721200287492206657)
        ·
          refine ⟨83567858790900215619154993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111423811721200287492206657 83567858790900215619154993)
          ·
            refine ⟨62675894093175161714366245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83567858790900215619154993 62675894093175161714366245)
            ·
              refine ⟨11751730142470342821443671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62675894093175161714366245 11751730142470342821443671)
              ·
                refine ⟨17627595213705514232165507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11751730142470342821443671 17627595213705514232165507)
                ·
                  refine ⟨26441392820558271348248261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17627595213705514232165507 26441392820558271348248261)
                  ·
                    refine ⟨4957761153854675877796549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26441392820558271348248261 4957761153854675877796549)
                    ·
                      refine ⟨929580216347751727086853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4957761153854675877796549 929580216347751727086853)
                      ·
                        rfl

theorem cell23_1810351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_1810351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810351 prefixEnd_1810351 := by exact prefixLift 1810351
  have htrace : WordTrace (prefixWord ++ tailWord_1810351) baseStart_1810351 baseEnd_1810351 := by
    simpa [prefixWord, tailWord_1810351, baseEnd_1810351] using wordTrace_append hprefix tailTrace_1810351
  have hstable : (prefixWord ++ tailWord_1810351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810351).length < 2 ^ (prefixWord ++ tailWord_1810351).sum := by decide
  have hdescent : baseEnd_1810351 < baseStart_1810351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810361 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 9]
def baseStart_1810361 : Nat := 118140960795 + 1810361 * 2 ^ 59
def prefixEnd_1810361 : Nat := 4983230072969 + 3 ^ 40 * 1810361 * 2
def baseEnd_1810361 : Nat := 103287261239366298662423

theorem tailTrace_1810361 : CollatzResearch.WordTrace tailWord_1810361 prefixEnd_1810361 103287261239366298662423 := by
  unfold tailWord_1810361
  simp only [CollatzResearch.WordTrace]
  refine ⟨66029290194378756888430937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44019526796252504592287291 66029290194378756888430937)
  ·
    refine ⟨49521967645784067666323203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66029290194378756888430937 49521967645784067666323203)
    ·
      refine ⟨74282951468676101499484805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49521967645784067666323203 74282951468676101499484805)
      ·
        refine ⟨13928053400376769031153401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74282951468676101499484805 13928053400376769031153401)
        ·
          refine ⟨10446040050282576773365051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13928053400376769031153401 10446040050282576773365051)
          ·
            refine ⟨15669060075423865160047577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446040050282576773365051 15669060075423865160047577)
            ·
              refine ⟨11751795056567898870035683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15669060075423865160047577 11751795056567898870035683)
              ·
                refine ⟨17627692584851848305053525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11751795056567898870035683 17627692584851848305053525)
                ·
                  refine ⟨103287261239366298662423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17627692584851848305053525 103287261239366298662423)
                  ·
                    rfl

theorem cell23_1810361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 9].length) (baseStart_1810361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810361 prefixEnd_1810361 := by exact prefixLift 1810361
  have htrace : WordTrace (prefixWord ++ tailWord_1810361) baseStart_1810361 baseEnd_1810361 := by
    simpa [prefixWord, tailWord_1810361, baseEnd_1810361] using wordTrace_append hprefix tailTrace_1810361
  have hstable : (prefixWord ++ tailWord_1810361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810361).length < 2 ^ (prefixWord ++ tailWord_1810361).sum := by decide
  have hdescent : baseEnd_1810361 < baseStart_1810361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810389 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_1810389 : Nat := 118140960795 + 1810389 * 2 ^ 59
def prefixEnd_1810389 : Nat := 4983230072969 + 3 ^ 40 * 1810389 * 2
def baseEnd_1810389 : Nat := 929599728612622578411679

theorem tailTrace_1810389 : CollatzResearch.WordTrace tailWord_1810389 prefixEnd_1810389 929599728612622578411679 := by
  unfold tailWord_1810389
  simp only [CollatzResearch.WordTrace]
  refine ⟨66030311438277317670450221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44020207625518211780300147 66030311438277317670450221)
  ·
    refine ⟨24761366789353994126418833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66030311438277317670450221 24761366789353994126418833)
    ·
      refine ⟨18571025092015495594814125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24761366789353994126418833 18571025092015495594814125)
      ·
        refine ⟨6964134409505810848055297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18571025092015495594814125 6964134409505810848055297)
        ·
          refine ⟨5223100807129358136041473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6964134409505810848055297 5223100807129358136041473)
          ·
            refine ⟨3917325605347018602031105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5223100807129358136041473 3917325605347018602031105)
            ·
              refine ⟨2937994204010263951523329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917325605347018602031105 2937994204010263951523329)
              ·
                refine ⟨2203495653007697963642497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937994204010263951523329 2203495653007697963642497)
                ·
                  refine ⟨1652621739755773472731873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2203495653007697963642497 1652621739755773472731873)
                  ·
                    refine ⟨1239466304816830104548905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1652621739755773472731873 1239466304816830104548905)
                    ·
                      refine ⟨929599728612622578411679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239466304816830104548905 929599728612622578411679)
                      ·
                        rfl

theorem cell23_1810389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_1810389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810389 prefixEnd_1810389 := by exact prefixLift 1810389
  have htrace : WordTrace (prefixWord ++ tailWord_1810389) baseStart_1810389 baseEnd_1810389 := by
    simpa [prefixWord, tailWord_1810389, baseEnd_1810389] using wordTrace_append hprefix tailTrace_1810389
  have hstable : (prefixWord ++ tailWord_1810389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810389).length < 2 ^ (prefixWord ++ tailWord_1810389).sum := by decide
  have hdescent : baseEnd_1810389 < baseStart_1810389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810402 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1810402 : Nat := 118140960795 + 1810402 * 2 ^ 59
def prefixEnd_1810402 : Nat := 4983230072969 + 3 ^ 40 * 1810402 * 2
def baseEnd_1810402 : Nat := 929606403861131027549119

theorem tailTrace_1810402 : CollatzResearch.WordTrace tailWord_1810402 prefixEnd_1810402 929606403861131027549119 := by
  unfold tailWord_1810402
  simp only [CollatzResearch.WordTrace]
  refine ⟨16507696396807555222668365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44020523724820147260448973 16507696396807555222668365)
  ·
    refine ⟨6190386148802833208500637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16507696396807555222668365 6190386148802833208500637)
    ·
      refine ⟨2321394805801062453187739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6190386148802833208500637 2321394805801062453187739)
      ·
        refine ⟨3482092208701593679781609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2321394805801062453187739 3482092208701593679781609)
        ·
          refine ⟨2611569156526195259836207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3482092208701593679781609 2611569156526195259836207)
          ·
            refine ⟨3917353734789292889754311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611569156526195259836207 3917353734789292889754311)
            ·
              refine ⟨5876030602183939334631467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917353734789292889754311 5876030602183939334631467)
              ·
                refine ⟨8814045903275909001947201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876030602183939334631467 8814045903275909001947201)
                ·
                  refine ⟨6610534427456931751460401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8814045903275909001947201 6610534427456931751460401)
                  ·
                    refine ⟨4957900820592698813595301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6610534427456931751460401 4957900820592698813595301)
                    ·
                      refine ⟨929606403861131027549119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4957900820592698813595301 929606403861131027549119)
                      ·
                        rfl

theorem cell23_1810402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1810402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810402 prefixEnd_1810402 := by exact prefixLift 1810402
  have htrace : WordTrace (prefixWord ++ tailWord_1810402) baseStart_1810402 baseEnd_1810402 := by
    simpa [prefixWord, tailWord_1810402, baseEnd_1810402] using wordTrace_append hprefix tailTrace_1810402
  have hstable : (prefixWord ++ tailWord_1810402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810402).length < 2 ^ (prefixWord ++ tailWord_1810402).sum := by decide
  have hdescent : baseEnd_1810402 < baseStart_1810402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
