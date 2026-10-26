import V185TrunkScan23Chunk0032

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_195736 : List Nat := [2, 1, 2, 4, 2, 1, 1, 5, 1, 2, 2]
def baseStart_195736 : Nat := 118140960795 + 195736 * 2 ^ 59
def prefixEnd_195736 : Nat := 4983230072969 + 3 ^ 40 * 195736 * 2
def baseEnd_195736 : Nat := 100506649388551415699833

theorem tailTrace_195736 : CollatzResearch.WordTrace tailWord_195736 prefixEnd_195736 100506649388551415699833 := by
  unfold tailWord_195736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3569539209444687946243531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4759385612592917261658041 3569539209444687946243531)
  ·
    refine ⟨5354308814167031919365297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3569539209444687946243531 5354308814167031919365297)
    ·
      refine ⟨4015731610625273939523973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5354308814167031919365297 4015731610625273939523973)
      ·
        refine ⟨752949676992238863660745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4015731610625273939523973 752949676992238863660745)
        ·
          refine ⟨564712257744179147745559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 752949676992238863660745 564712257744179147745559)
          ·
            refine ⟨847068386616268721618339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564712257744179147745559 847068386616268721618339)
            ·
              refine ⟨1270602579924403082427509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847068386616268721618339 1270602579924403082427509)
              ·
                refine ⟨119118991867912788977579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1270602579924403082427509 119118991867912788977579)
                ·
                  refine ⟨178678487801869183466369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119118991867912788977579 178678487801869183466369)
                  ·
                    refine ⟨134008865851401887599777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178678487801869183466369 134008865851401887599777)
                    ·
                      refine ⟨100506649388551415699833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134008865851401887599777 100506649388551415699833)
                      ·
                        rfl

theorem cell23_195736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_195736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195736 prefixEnd_195736 := by exact prefixLift 195736
  have htrace : WordTrace (prefixWord ++ tailWord_195736) baseStart_195736 baseEnd_195736 := by
    simpa [prefixWord, tailWord_195736, baseEnd_195736] using wordTrace_append hprefix tailTrace_195736
  have hstable : (prefixWord ++ tailWord_195736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195736).length < 2 ^ (prefixWord ++ tailWord_195736).sum := by decide
  have hdescent : baseEnd_195736 < baseStart_195736 := by decide
  rcases family_descends (prefixWord ++ tailWord_195736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195746 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_195746 : Nat := 118140960795 + 195746 * 2 ^ 59
def prefixEnd_195746 : Nat := 4983230072969 + 3 ^ 40 * 195746 * 2
def baseEnd_195746 : Nat := 33503928065032125524929

theorem tailTrace_195746 : CollatzResearch.WordTrace tailWord_195746 prefixEnd_195746 33503928065032125524929 := by
  unfold tailWord_195746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784860787213286900087773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4759628765902098400234061 1784860787213286900087773)
  ·
    refine ⟨669322795204982587532915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1784860787213286900087773 669322795204982587532915)
    ·
      refine ⟨1003984192807473881299373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 669322795204982587532915 1003984192807473881299373)
      ·
        refine ⟨376494072302802705487265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1003984192807473881299373 376494072302802705487265)
        ·
          refine ⟨282370554227102029115449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376494072302802705487265 282370554227102029115449)
          ·
            refine ⟨211777915670326521836587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282370554227102029115449 211777915670326521836587)
            ·
              refine ⟨317666873505489782754881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211777915670326521836587 317666873505489782754881)
              ·
                refine ⟨238250155129117337066161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317666873505489782754881 238250155129117337066161)
                ·
                  refine ⟨178687616346838002799621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238250155129117337066161 178687616346838002799621)
                  ·
                    refine ⟨33503928065032125524929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 178687616346838002799621 33503928065032125524929)
                    ·
                      rfl

theorem cell23_195746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_195746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195746 prefixEnd_195746 := by exact prefixLift 195746
  have htrace : WordTrace (prefixWord ++ tailWord_195746) baseStart_195746 baseEnd_195746 := by
    simpa [prefixWord, tailWord_195746, baseEnd_195746] using wordTrace_append hprefix tailTrace_195746
  have hstable : (prefixWord ++ tailWord_195746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195746).length < 2 ^ (prefixWord ++ tailWord_195746).sum := by decide
  have hdescent : baseEnd_195746 < baseStart_195746 := by decide
  rcases family_descends (prefixWord ++ tailWord_195746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195768 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 1, 8]
def baseStart_195768 : Nat := 118140960795 + 195768 * 2 ^ 59
def prefixEnd_195768 : Nat := 4983230072969 + 3 ^ 40 * 195768 * 2
def baseEnd_195768 : Nat := 33507693589831763499895

theorem tailTrace_195768 : CollatzResearch.WordTrace tailWord_195768 prefixEnd_195768 33507693589831763499895 := by
  unfold tailWord_195768
  simp only [CollatzResearch.WordTrace]
  refine ⟨3570122777386722678825979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4760163703182296905101305 3570122777386722678825979)
  ·
    refine ⟨5355184166080084018238969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3570122777386722678825979 5355184166080084018238969)
    ·
      refine ⟨4016388124560063013679227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5355184166080084018238969 4016388124560063013679227)
      ·
        refine ⟨6024582186840094520518841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4016388124560063013679227 6024582186840094520518841)
        ·
          refine ⟨4518436640130070890389131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6024582186840094520518841 4518436640130070890389131)
          ·
            refine ⟨6777654960195106335583697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518436640130070890389131 6777654960195106335583697)
            ·
              refine ⟨5083241220146329751687773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6777654960195106335583697 5083241220146329751687773)
              ·
                refine ⟨1906215457554873656882915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5083241220146329751687773 1906215457554873656882915)
                ·
                  refine ⟨2859323186332310485324373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906215457554873656882915 2859323186332310485324373)
                  ·
                    refine ⟨33507693589831763499895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2859323186332310485324373 33507693589831763499895)
                    ·
                      rfl

theorem cell23_195768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_195768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195768 prefixEnd_195768 := by exact prefixLift 195768
  have htrace : WordTrace (prefixWord ++ tailWord_195768) baseStart_195768 baseEnd_195768 := by
    simpa [prefixWord, tailWord_195768, baseEnd_195768] using wordTrace_append hprefix tailTrace_195768
  have hstable : (prefixWord ++ tailWord_195768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195768).length < 2 ^ (prefixWord ++ tailWord_195768).sum := by decide
  have hdescent : baseEnd_195768 < baseStart_195768 := by decide
  rcases family_descends (prefixWord ++ tailWord_195768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195809 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_195809 : Nat := 118140960795 + 195809 * 2 ^ 59
def prefixEnd_195809 : Nat := 4983230072969 + 3 ^ 40 * 195809 * 2
def baseEnd_195809 : Nat := 100544133476329630086997

theorem tailTrace_195809 : CollatzResearch.WordTrace tailWord_195809 prefixEnd_195809 100544133476329630086997 := by
  unfold tailWord_195809
  simp only [CollatzResearch.WordTrace]
  refine ⟨7141740947624909359894481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4761160631749939573262987 7141740947624909359894481)
  ·
    refine ⟨5356305710718682019920861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7141740947624909359894481 5356305710718682019920861)
    ·
      refine ⟨2008614641519505757470323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5356305710718682019920861 2008614641519505757470323)
      ·
        refine ⟨3012921962279258636205485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008614641519505757470323 3012921962279258636205485)
        ·
          refine ⟨1129845735854721988577057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3012921962279258636205485 1129845735854721988577057)
          ·
            refine ⟨847384301891041491432793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1129845735854721988577057 847384301891041491432793)
            ·
              refine ⟨635538226418281118574595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847384301891041491432793 635538226418281118574595)
              ·
                refine ⟨953307339627421677861893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635538226418281118574595 953307339627421677861893)
                ·
                  refine ⟨178745126180141564599105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953307339627421677861893 178745126180141564599105)
                  ·
                    refine ⟨134058844635106173449329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178745126180141564599105 134058844635106173449329)
                    ·
                      refine ⟨100544133476329630086997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134058844635106173449329 100544133476329630086997)
                      ·
                        rfl

theorem cell23_195809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_195809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195809 prefixEnd_195809 := by exact prefixLift 195809
  have htrace : WordTrace (prefixWord ++ tailWord_195809) baseStart_195809 baseEnd_195809 := by
    simpa [prefixWord, tailWord_195809, baseEnd_195809] using wordTrace_append hprefix tailTrace_195809
  have hstable : (prefixWord ++ tailWord_195809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195809).length < 2 ^ (prefixWord ++ tailWord_195809).sum := by decide
  have hdescent : baseEnd_195809 < baseStart_195809 := by decide
  rcases family_descends (prefixWord ++ tailWord_195809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195825 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_195825 : Nat := 118140960795 + 195825 * 2 ^ 59
def prefixEnd_195825 : Nat := 4983230072969 + 3 ^ 40 * 195825 * 2
def baseEnd_195825 : Nat := 100552349166801567486923

theorem tailTrace_195825 : CollatzResearch.WordTrace tailWord_195825 prefixEnd_195825 100552349166801567486923 := by
  unfold tailWord_195825
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142324515566944092476929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4761549677044629394984619 7142324515566944092476929)
  ·
    refine ⟨5356743386675208069357697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7142324515566944092476929 5356743386675208069357697)
    ·
      refine ⟨4017557540006406052018273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5356743386675208069357697 4017557540006406052018273)
      ·
        refine ⟨3013168155004804539013705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017557540006406052018273 3013168155004804539013705)
        ·
          refine ⟨2259876116253603404260279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3013168155004804539013705 2259876116253603404260279)
          ·
            refine ⟨3389814174380405106390419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259876116253603404260279 3389814174380405106390419)
            ·
              refine ⟨5084721261570607659585629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389814174380405106390419 5084721261570607659585629)
              ·
                refine ⟨1906770473088977872344611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5084721261570607659585629 1906770473088977872344611)
                ·
                  refine ⟨2860155709633466808516917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906770473088977872344611 2860155709633466808516917)
                  ·
                    refine ⟨268139597778137513298461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2860155709633466808516917 268139597778137513298461)
                    ·
                      refine ⟨100552349166801567486923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 268139597778137513298461 100552349166801567486923)
                      ·
                        rfl

theorem cell23_195825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_195825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195825 prefixEnd_195825 := by exact prefixLift 195825
  have htrace : WordTrace (prefixWord ++ tailWord_195825) baseStart_195825 baseEnd_195825 := by
    simpa [prefixWord, tailWord_195825, baseEnd_195825] using wordTrace_append hprefix tailTrace_195825
  have hstable : (prefixWord ++ tailWord_195825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195825).length < 2 ^ (prefixWord ++ tailWord_195825).sum := by decide
  have hdescent : baseEnd_195825 < baseStart_195825 := by decide
  rcases family_descends (prefixWord ++ tailWord_195825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195866 : List Nat := [3, 1, 1, 3, 3, 3, 2, 2, 5]
def baseStart_195866 : Nat := 118140960795 + 195866 * 2 ^ 59
def prefixEnd_195866 : Nat := 4983230072969 + 3 ^ 40 * 195866 * 2
def baseEnd_195866 : Nat := 11174822430403989674915

theorem tailTrace_195866 : CollatzResearch.WordTrace tailWord_195866 prefixEnd_195866 11174822430403989674915 := by
  unfold tailWord_195866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1785954977104602023679863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4762546605612272063146301 1785954977104602023679863)
  ·
    refine ⟨2678932465656903035519795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1785954977104602023679863 2678932465656903035519795)
    ·
      refine ⟨4018398698485354553279693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2678932465656903035519795 4018398698485354553279693)
      ·
        refine ⟨1506899511932007957479885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4018398698485354553279693 1506899511932007957479885)
        ·
          refine ⟨565087316974502984054957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1506899511932007957479885 565087316974502984054957)
          ·
            refine ⟨211907743865438619020609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 565087316974502984054957 211907743865438619020609)
            ·
              refine ⟨158930807899078964265457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211907743865438619020609 158930807899078964265457)
              ·
                refine ⟨119198105924309223199093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158930807899078964265457 119198105924309223199093)
                ·
                  refine ⟨11174822430403989674915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119198105924309223199093 11174822430403989674915)
                  ·
                    rfl

theorem cell23_195866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_195866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195866 prefixEnd_195866 := by exact prefixLift 195866
  have htrace : WordTrace (prefixWord ++ tailWord_195866) baseStart_195866 baseEnd_195866 := by
    simpa [prefixWord, tailWord_195866, baseEnd_195866] using wordTrace_append hprefix tailTrace_195866
  have hstable : (prefixWord ++ tailWord_195866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195866).length < 2 ^ (prefixWord ++ tailWord_195866).sum := by decide
  have hdescent : baseEnd_195866 < baseStart_195866 := by decide
  rcases family_descends (prefixWord ++ tailWord_195866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195869 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_195869 : Nat := 118140960795 + 195869 * 2 ^ 59
def prefixEnd_195869 : Nat := 4983230072969 + 3 ^ 40 * 195869 * 2
def baseEnd_195869 : Nat := 100574942315599395336721

theorem tailTrace_195869 : CollatzResearch.WordTrace tailWord_195869 prefixEnd_195869 100574942315599395336721 := by
  unfold tailWord_195869
  simp only [CollatzResearch.WordTrace]
  refine ⟨7143929327407539607078661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4762619551605026404719107 7143929327407539607078661)
  ·
    refine ⟨1339486748888913676327249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7143929327407539607078661 1339486748888913676327249)
    ·
      refine ⟨1004615061666685257245437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1339486748888913676327249 1004615061666685257245437)
      ·
        refine ⟨376730648125006971467039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1004615061666685257245437 376730648125006971467039)
        ·
          refine ⟨565095972187510457200559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376730648125006971467039 565095972187510457200559)
          ·
            refine ⟨847643958281265685800839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565095972187510457200559 847643958281265685800839)
            ·
              refine ⟨1271465937421898528701259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847643958281265685800839 1271465937421898528701259)
              ·
                refine ⟨1907198906132847793051889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271465937421898528701259 1907198906132847793051889)
                ·
                  refine ⟨1430399179599635844788917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1907198906132847793051889 1430399179599635844788917)
                  ·
                    refine ⟨134099923087465860448961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1430399179599635844788917 134099923087465860448961)
                    ·
                      refine ⟨100574942315599395336721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134099923087465860448961 100574942315599395336721)
                      ·
                        rfl

theorem cell23_195869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_195869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195869 prefixEnd_195869 := by exact prefixLift 195869
  have htrace : WordTrace (prefixWord ++ tailWord_195869) baseStart_195869 baseEnd_195869 := by
    simpa [prefixWord, tailWord_195869, baseEnd_195869] using wordTrace_append hprefix tailTrace_195869
  have hstable : (prefixWord ++ tailWord_195869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195869).length < 2 ^ (prefixWord ++ tailWord_195869).sum := by decide
  have hdescent : baseEnd_195869 < baseStart_195869 := by decide
  rcases family_descends (prefixWord ++ tailWord_195869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195939 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 6]
def baseStart_195939 : Nat := 118140960795 + 195939 * 2 ^ 59
def prefixEnd_195939 : Nat := 4983230072969 + 3 ^ 40 * 195939 * 2
def baseEnd_195939 : Nat := 11178987329046013495711

theorem tailTrace_195939 : CollatzResearch.WordTrace tailWord_195939 prefixEnd_195939 11178987329046013495711 := by
  unfold tailWord_195939
  simp only [CollatzResearch.WordTrace]
  refine ⟨7146482437153941562126871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4764321624769294374751247 7146482437153941562126871)
  ·
    refine ⟨10719723655730912343190307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7146482437153941562126871 10719723655730912343190307)
    ·
      refine ⟨16079585483596368514785461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10719723655730912343190307 16079585483596368514785461)
      ·
        refine ⟨1507461139087159548261137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16079585483596368514785461 1507461139087159548261137)
        ·
          refine ⟨1130595854315369661195853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1507461139087159548261137 1130595854315369661195853)
          ·
            refine ⟨423973445368263622948445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1130595854315369661195853 423973445368263622948445)
            ·
              refine ⟨158990042013098858605667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 423973445368263622948445 158990042013098858605667)
              ·
                refine ⟨238485063019648287908501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158990042013098858605667 238485063019648287908501)
                ·
                  refine ⟨11178987329046013495711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 238485063019648287908501 11178987329046013495711)
                  ·
                    rfl

theorem cell23_195939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 6].length) (baseStart_195939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195939 prefixEnd_195939 := by exact prefixLift 195939
  have htrace : WordTrace (prefixWord ++ tailWord_195939) baseStart_195939 baseEnd_195939 := by
    simpa [prefixWord, tailWord_195939, baseEnd_195939] using wordTrace_append hprefix tailTrace_195939
  have hstable : (prefixWord ++ tailWord_195939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195939).length < 2 ^ (prefixWord ++ tailWord_195939).sum := by decide
  have hdescent : baseEnd_195939 < baseStart_195939 := by decide
  rcases family_descends (prefixWord ++ tailWord_195939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195959 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 2, 3, 2]
def baseStart_195959 : Nat := 118140960795 + 195959 * 2 ^ 59
def prefixEnd_195959 : Nat := 4983230072969 + 3 ^ 40 * 195959 * 2
def baseEnd_195959 : Nat := 100621155574504043211307

theorem tailTrace_195959 : CollatzResearch.WordTrace tailWord_195959 prefixEnd_195959 100621155574504043211307 := by
  unfold tailWord_195959
  simp only [CollatzResearch.WordTrace]
  refine ⟨7147211897081484977854931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4764807931387656651903287 7147211897081484977854931)
  ·
    refine ⟨10720817845622227466782397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7147211897081484977854931 10720817845622227466782397)
    ·
      refine ⟨4020306692108335300043399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10720817845622227466782397 4020306692108335300043399)
      ·
        refine ⟨6030460038162502950065099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020306692108335300043399 6030460038162502950065099)
        ·
          refine ⟨9045690057243754425097649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6030460038162502950065099 9045690057243754425097649)
          ·
            refine ⟨6784267542932815818823237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9045690057243754425097649 6784267542932815818823237)
            ·
              refine ⟨1272050164299902966029357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6784267542932815818823237 1272050164299902966029357)
              ·
                refine ⟨477018811612463612261009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1272050164299902966029357 477018811612463612261009)
                ·
                  refine ⟨357764108709347709195757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477018811612463612261009 357764108709347709195757)
                  ·
                    refine ⟨134161540766005390948409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357764108709347709195757 134161540766005390948409)
                    ·
                      refine ⟨100621155574504043211307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134161540766005390948409 100621155574504043211307)
                      ·
                        rfl

theorem cell23_195959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_195959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195959 prefixEnd_195959 := by exact prefixLift 195959
  have htrace : WordTrace (prefixWord ++ tailWord_195959) baseStart_195959 baseEnd_195959 := by
    simpa [prefixWord, tailWord_195959, baseEnd_195959] using wordTrace_append hprefix tailTrace_195959
  have hstable : (prefixWord ++ tailWord_195959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195959).length < 2 ^ (prefixWord ++ tailWord_195959).sum := by decide
  have hdescent : baseEnd_195959 < baseStart_195959 := by decide
  rcases family_descends (prefixWord ++ tailWord_195959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195976 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_195976 : Nat := 118140960795 + 195976 * 2 ^ 59
def prefixEnd_195976 : Nat := 4983230072969 + 3 ^ 40 * 195976 * 2
def baseEnd_195976 : Nat := 100629884745630476698729

theorem tailTrace_195976 : CollatzResearch.WordTrace tailWord_195976 prefixEnd_195976 100629884745630476698729 := by
  unfold tailWord_195976
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573915969009948440611891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4765221292013264587482521 3573915969009948440611891)
  ·
    refine ⟨5360873953514922660917837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3573915969009948440611891 5360873953514922660917837)
    ·
      refine ⟨2010327732568095997844189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5360873953514922660917837 2010327732568095997844189)
      ·
        refine ⟨753872899713035999191571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2010327732568095997844189 753872899713035999191571)
        ·
          refine ⟨1130809349569553998787357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753872899713035999191571 1130809349569553998787357)
          ·
            refine ⟨424053506088582749545259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1130809349569553998787357 424053506088582749545259)
            ·
              refine ⟨636080259132874124317889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424053506088582749545259 636080259132874124317889)
              ·
                refine ⟨477060194349655593238417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636080259132874124317889 477060194349655593238417)
                ·
                  refine ⟨357795145762241694928813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477060194349655593238417 357795145762241694928813)
                  ·
                    refine ⟨134173179660840635598305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357795145762241694928813 134173179660840635598305)
                    ·
                      refine ⟨100629884745630476698729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134173179660840635598305 100629884745630476698729)
                      ·
                        rfl

theorem cell23_195976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_195976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195976 prefixEnd_195976 := by exact prefixLift 195976
  have htrace : WordTrace (prefixWord ++ tailWord_195976) baseStart_195976 baseEnd_195976 := by
    simpa [prefixWord, tailWord_195976, baseEnd_195976] using wordTrace_append hprefix tailTrace_195976
  have hstable : (prefixWord ++ tailWord_195976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195976).length < 2 ^ (prefixWord ++ tailWord_195976).sum := by decide
  have hdescent : baseEnd_195976 < baseStart_195976 := by decide
  rcases family_descends (prefixWord ++ tailWord_195976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196023 : List Nat := [1, 1, 3, 1, 3, 2, 2, 5, 1, 2, 2]
def baseStart_196023 : Nat := 118140960795 + 196023 * 2 ^ 59
def prefixEnd_196023 : Nat := 4983230072969 + 3 ^ 40 * 196023 * 2
def baseEnd_196023 : Nat := 100654018336391792811013

theorem tailTrace_196023 : CollatzResearch.WordTrace tailWord_196023 prefixEnd_196023 100654018336391792811013 := by
  unfold tailWord_196023
  simp only [CollatzResearch.WordTrace]
  refine ⟨7149546168849623908184723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4766364112566415938789815 7149546168849623908184723)
  ·
    refine ⟨10724319253274435862277085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7149546168849623908184723 10724319253274435862277085)
    ·
      refine ⟨4021619719977913448353907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10724319253274435862277085 4021619719977913448353907)
      ·
        refine ⟨6032429579966870172530861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4021619719977913448353907 6032429579966870172530861)
        ·
          refine ⟨2262161092487576314699073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6032429579966870172530861 2262161092487576314699073)
          ·
            refine ⟨1696620819365682236024305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2262161092487576314699073 1696620819365682236024305)
            ·
              refine ⟨1272465614524261677018229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696620819365682236024305 1272465614524261677018229)
              ·
                refine ⟨119293651361649532220459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1272465614524261677018229 119293651361649532220459)
                ·
                  refine ⟨178940477042474298330689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119293651361649532220459 178940477042474298330689)
                  ·
                    refine ⟨134205357781855723748017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178940477042474298330689 134205357781855723748017)
                    ·
                      refine ⟨100654018336391792811013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134205357781855723748017 100654018336391792811013)
                      ·
                        rfl

theorem cell23_196023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 2, 2].length) (baseStart_196023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196023 prefixEnd_196023 := by exact prefixLift 196023
  have htrace : WordTrace (prefixWord ++ tailWord_196023) baseStart_196023 baseEnd_196023 := by
    simpa [prefixWord, tailWord_196023, baseEnd_196023] using wordTrace_append hprefix tailTrace_196023
  have hstable : (prefixWord ++ tailWord_196023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196023).length < 2 ^ (prefixWord ++ tailWord_196023).sum := by decide
  have hdescent : baseEnd_196023 < baseStart_196023 := by decide
  rcases family_descends (prefixWord ++ tailWord_196023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196042 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_196042 : Nat := 118140960795 + 196042 * 2 ^ 59
def prefixEnd_196042 : Nat := 4983230072969 + 3 ^ 40 * 196042 * 2
def baseEnd_196042 : Nat := 33554591489609072824475

theorem tailTrace_196042 : CollatzResearch.WordTrace tailWord_196042 prefixEnd_196042 33554591489609072824475 := by
  unfold tailWord_196042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1787559788945197538281595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4766826103853860102084253 1787559788945197538281595)
  ·
    refine ⟨2681339683417796307422393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1787559788945197538281595 2681339683417796307422393)
    ·
      refine ⟨2011004762563347230566795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2681339683417796307422393 2011004762563347230566795)
      ·
        refine ⟨3016507143845020845850193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2011004762563347230566795 3016507143845020845850193)
        ·
          refine ⟨2262380357883765634387645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3016507143845020845850193 2262380357883765634387645)
          ·
            refine ⟨848392634206412112895367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2262380357883765634387645 848392634206412112895367)
            ·
              refine ⟨1272588951309618169343051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848392634206412112895367 1272588951309618169343051)
              ·
                refine ⟨1908883426964427254014577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272588951309618169343051 1908883426964427254014577)
                ·
                  refine ⟨1431662570223320440510933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1908883426964427254014577 1431662570223320440510933)
                  ·
                    refine ⟨33554591489609072824475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1431662570223320440510933 33554591489609072824475)
                    ·
                      rfl

theorem cell23_196042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_196042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196042 prefixEnd_196042 := by exact prefixLift 196042
  have htrace : WordTrace (prefixWord ++ tailWord_196042) baseStart_196042 baseEnd_196042 := by
    simpa [prefixWord, tailWord_196042, baseEnd_196042] using wordTrace_append hprefix tailTrace_196042
  have hstable : (prefixWord ++ tailWord_196042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196042).length < 2 ^ (prefixWord ++ tailWord_196042).sum := by decide
  have hdescent : baseEnd_196042 < baseStart_196042 := by decide
  rcases family_descends (prefixWord ++ tailWord_196042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196056 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 2, 1, 3]
def baseStart_196056 : Nat := 118140960795 + 196056 * 2 ^ 59
def prefixEnd_196056 : Nat := 4983230072969 + 3 ^ 40 * 196056 * 2
def baseEnd_196056 : Nat := 100670963197990163698361

theorem tailTrace_196056 : CollatzResearch.WordTrace tailWord_196056 prefixEnd_196056 100670963197990163698361 := by
  unfold tailWord_196056
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575374888865035272068011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4767166518486713696090681 3575374888865035272068011)
  ·
    refine ⟨5363062333297552908102017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3575374888865035272068011 5363062333297552908102017)
    ·
      refine ⟨4022296749973164681076513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5363062333297552908102017 4022296749973164681076513)
      ·
        refine ⟨3016722562479873510807385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4022296749973164681076513 3016722562479873510807385)
        ·
          refine ⟨2262541921859905133105539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3016722562479873510807385 2262541921859905133105539)
          ·
            refine ⟨3393812882789857699658309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262541921859905133105539 3393812882789857699658309)
            ·
              refine ⟨636339915523098318685933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3393812882789857699658309 636339915523098318685933)
              ·
                refine ⟨238627468321161869507225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 636339915523098318685933 238627468321161869507225)
                ·
                  refine ⟨178970601240871402130419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238627468321161869507225 178970601240871402130419)
                  ·
                    refine ⟨268455901861307103195629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178970601240871402130419 268455901861307103195629)
                    ·
                      refine ⟨100670963197990163698361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 268455901861307103195629 100670963197990163698361)
                      ·
                        rfl

theorem cell23_196056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_196056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196056 prefixEnd_196056 := by exact prefixLift 196056
  have htrace : WordTrace (prefixWord ++ tailWord_196056) baseStart_196056 baseEnd_196056 := by
    simpa [prefixWord, tailWord_196056, baseEnd_196056] using wordTrace_append hprefix tailTrace_196056
  have hstable : (prefixWord ++ tailWord_196056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196056).length < 2 ^ (prefixWord ++ tailWord_196056).sum := by decide
  have hdescent : baseEnd_196056 < baseStart_196056 := by decide
  rcases family_descends (prefixWord ++ tailWord_196056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196072 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 1, 8]
def baseStart_196072 : Nat := 118140960795 + 196072 * 2 ^ 59
def prefixEnd_196072 : Nat := 4983230072969 + 3 ^ 40 * 196072 * 2
def baseEnd_196072 : Nat := 33559726296154033699429

theorem tailTrace_196072 : CollatzResearch.WordTrace tailWord_196072 prefixEnd_196072 33559726296154033699429 := by
  unfold tailWord_196072
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575666672836052638359235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4767555563781403517812313 3575666672836052638359235)
  ·
    refine ⟨5363500009254078957538853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3575666672836052638359235 5363500009254078957538853)
    ·
      refine ⟨1005656251735139804538535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5363500009254078957538853 1005656251735139804538535)
      ·
        refine ⟨1508484377602709706807803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1005656251735139804538535 1508484377602709706807803)
        ·
          refine ⟨2262726566404064560211705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508484377602709706807803 2262726566404064560211705)
          ·
            refine ⟨1697044924803048420158779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2262726566404064560211705 1697044924803048420158779)
            ·
              refine ⟨2545567387204572630238169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697044924803048420158779 2545567387204572630238169)
              ·
                refine ⟨1909175540403429472678627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2545567387204572630238169 1909175540403429472678627)
                ·
                  refine ⟨2863763310605144209017941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909175540403429472678627 2863763310605144209017941)
                  ·
                    refine ⟨33559726296154033699429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2863763310605144209017941 33559726296154033699429)
                    ·
                      rfl

theorem cell23_196072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_196072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196072 prefixEnd_196072 := by exact prefixLift 196072
  have htrace : WordTrace (prefixWord ++ tailWord_196072) baseStart_196072 baseEnd_196072 := by
    simpa [prefixWord, tailWord_196072, baseEnd_196072] using wordTrace_append hprefix tailTrace_196072
  have hstable : (prefixWord ++ tailWord_196072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196072).length < 2 ^ (prefixWord ++ tailWord_196072).sum := by decide
  have hdescent : baseEnd_196072 < baseStart_196072 := by decide
  rcases family_descends (prefixWord ++ tailWord_196072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196077 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_196077 : Nat := 118140960795 + 196077 * 2 ^ 59
def prefixEnd_196077 : Nat := 4983230072969 + 3 ^ 40 * 196077 * 2
def baseEnd_196077 : Nat := 100681746291734581535765

theorem tailTrace_196077 : CollatzResearch.WordTrace tailWord_196077 prefixEnd_196077 100681746291734581535765 := by
  unfold tailWord_196077
  simp only [CollatzResearch.WordTrace]
  refine ⟨7151515710653991130650485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4767677140435994087100323 7151515710653991130650485)
  ·
    refine ⟨670454597873811668498483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7151515710653991130650485 670454597873811668498483)
    ·
      refine ⟨1005681896810717502747725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670454597873811668498483 1005681896810717502747725)
      ·
        refine ⟨377130711304019063530397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1005681896810717502747725 377130711304019063530397)
        ·
          refine ⟨141424016739007148823899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377130711304019063530397 141424016739007148823899)
          ·
            refine ⟨212136025108510723235849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141424016739007148823899 212136025108510723235849)
            ·
              refine ⟨159102018831383042426887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212136025108510723235849 159102018831383042426887)
              ·
                refine ⟨238653028247074563640331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159102018831383042426887 238653028247074563640331)
                ·
                  refine ⟨357979542370611845460497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238653028247074563640331 357979542370611845460497)
                  ·
                    refine ⟨268484656777958884095373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357979542370611845460497 268484656777958884095373)
                    ·
                      refine ⟨100681746291734581535765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 268484656777958884095373 100681746291734581535765)
                      ·
                        rfl

theorem cell23_196077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_196077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196077 prefixEnd_196077 := by exact prefixLift 196077
  have htrace : WordTrace (prefixWord ++ tailWord_196077) baseStart_196077 baseEnd_196077 := by
    simpa [prefixWord, tailWord_196077, baseEnd_196077] using wordTrace_append hprefix tailTrace_196077
  have hstable : (prefixWord ++ tailWord_196077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196077).length < 2 ^ (prefixWord ++ tailWord_196077).sum := by decide
  have hdescent : baseEnd_196077 < baseStart_196077 := by decide
  rcases family_descends (prefixWord ++ tailWord_196077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196139 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 3, 7, 2]
def baseStart_196139 : Nat := 118140960795 + 196139 * 2 ^ 59
def prefixEnd_196139 : Nat := 4983230072969 + 3 ^ 40 * 196139 * 2
def baseEnd_196139 : Nat := 100713582092313338960479

theorem tailTrace_196139 : CollatzResearch.WordTrace tailWord_196139 prefixEnd_196139 100713582092313338960479 := by
  unfold tailWord_196139
  simp only [CollatzResearch.WordTrace]
  refine ⟨7153777036429375719407471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4769184690952917146271647 7153777036429375719407471)
  ·
    refine ⟨10730665554644063579111207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7153777036429375719407471 10730665554644063579111207)
    ·
      refine ⟨16095998331966095368666811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10730665554644063579111207 16095998331966095368666811)
      ·
        refine ⟨24143997497949143053000217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16095998331966095368666811 24143997497949143053000217)
        ·
          refine ⟨18107998123461857289750163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24143997497949143053000217 18107998123461857289750163)
          ·
            refine ⟨27161997185192785934625245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18107998123461857289750163 27161997185192785934625245)
            ·
              refine ⟨10185748944447294725484467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27161997185192785934625245 10185748944447294725484467)
              ·
                refine ⟨15278623416670942088226701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10185748944447294725484467 15278623416670942088226701)
                ·
                  refine ⟨5729483781251603283085013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15278623416670942088226701 5729483781251603283085013)
                  ·
                    refine ⟨134284776123084451947305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5729483781251603283085013 134284776123084451947305)
                    ·
                      refine ⟨100713582092313338960479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134284776123084451947305 100713582092313338960479)
                      ·
                        rfl

theorem cell23_196139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 7, 2].length) (baseStart_196139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196139 prefixEnd_196139 := by exact prefixLift 196139
  have htrace : WordTrace (prefixWord ++ tailWord_196139) baseStart_196139 baseEnd_196139 := by
    simpa [prefixWord, tailWord_196139, baseEnd_196139] using wordTrace_append hprefix tailTrace_196139
  have hstable : (prefixWord ++ tailWord_196139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196139).length < 2 ^ (prefixWord ++ tailWord_196139).sum := by decide
  have hdescent : baseEnd_196139 < baseStart_196139 := by decide
  rcases family_descends (prefixWord ++ tailWord_196139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196149 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_196149 : Nat := 118140960795 + 196149 * 2 ^ 59
def prefixEnd_196149 : Nat := 4983230072969 + 3 ^ 40 * 196149 * 2
def baseEnd_196149 : Nat := 33572905632952766611811

theorem tailTrace_196149 : CollatzResearch.WordTrace tailWord_196149 prefixEnd_196149 33572905632952766611811 := by
  unfold tailWord_196149
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154141766393147427271501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4769427844262098284847667 7154141766393147427271501)
  ·
    refine ⟨2682803162397430285226813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7154141766393147427271501 2682803162397430285226813)
    ·
      refine ⟨1006051185899036356960055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2682803162397430285226813 1006051185899036356960055)
      ·
        refine ⟨1509076778848554535440083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006051185899036356960055 1509076778848554535440083)
        ·
          refine ⟨2263615168272831803160125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509076778848554535440083 2263615168272831803160125)
          ·
            refine ⟨848855688102311926185047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2263615168272831803160125 848855688102311926185047)
            ·
              refine ⟨1273283532153467889277571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848855688102311926185047 1273283532153467889277571)
              ·
                refine ⟨1909925298230201833916357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273283532153467889277571 1909925298230201833916357)
                ·
                  refine ⟨358110993418162843859317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1909925298230201833916357 358110993418162843859317)
                  ·
                    refine ⟨33572905632952766611811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 358110993418162843859317 33572905632952766611811)
                    ·
                      rfl

theorem cell23_196149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_196149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196149 prefixEnd_196149 := by exact prefixLift 196149
  have htrace : WordTrace (prefixWord ++ tailWord_196149) baseStart_196149 baseEnd_196149 := by
    simpa [prefixWord, tailWord_196149, baseEnd_196149] using wordTrace_append hprefix tailTrace_196149
  have hstable : (prefixWord ++ tailWord_196149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196149).length < 2 ^ (prefixWord ++ tailWord_196149).sum := by decide
  have hdescent : baseEnd_196149 < baseStart_196149 := by decide
  rcases family_descends (prefixWord ++ tailWord_196149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196153 : List Nat := [1, 2, 1, 5, 1, 3, 3, 2, 5]
def baseStart_196153 : Nat := 118140960795 + 196153 * 2 ^ 59
def prefixEnd_196153 : Nat := 4983230072969 + 3 ^ 40 * 196153 * 2
def baseEnd_196153 : Nat := 11191196757941809353935

theorem tailTrace_196153 : CollatzResearch.WordTrace tailWord_196153 prefixEnd_196153 11191196757941809353935 := by
  unfold tailWord_196153
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154287658378656110417113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4769525105585770740278075 7154287658378656110417113)
  ·
    refine ⟨5365715743783992082812835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7154287658378656110417113 5365715743783992082812835)
    ·
      refine ⟨8048573615675988124219253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5365715743783992082812835 8048573615675988124219253)
      ·
        refine ⟨754553776469623886645555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8048573615675988124219253 754553776469623886645555)
        ·
          refine ⟨1131830664704435829968333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754553776469623886645555 1131830664704435829968333)
          ·
            refine ⟨424436499264163436238125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1131830664704435829968333 424436499264163436238125)
            ·
              refine ⟨159163687224061288589297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424436499264163436238125 159163687224061288589297)
              ·
                refine ⟨119372765418045966441973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159163687224061288589297 119372765418045966441973)
                ·
                  refine ⟨11191196757941809353935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119372765418045966441973 11191196757941809353935)
                  ·
                    rfl

theorem cell23_196153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 5].length) (baseStart_196153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196153 prefixEnd_196153 := by exact prefixLift 196153
  have htrace : WordTrace (prefixWord ++ tailWord_196153) baseStart_196153 baseEnd_196153 := by
    simpa [prefixWord, tailWord_196153, baseEnd_196153] using wordTrace_append hprefix tailTrace_196153
  have hstable : (prefixWord ++ tailWord_196153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196153).length < 2 ^ (prefixWord ++ tailWord_196153).sum := by decide
  have hdescent : baseEnd_196153 < baseStart_196153 := by decide
  rcases family_descends (prefixWord ++ tailWord_196153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196159 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_196159 : Nat := 118140960795 + 196159 * 2 ^ 59
def prefixEnd_196159 : Nat := 4983230072969 + 3 ^ 40 * 196159 * 2
def baseEnd_196159 : Nat := 100723851705403260710387

theorem tailTrace_196159 : CollatzResearch.WordTrace tailWord_196159 prefixEnd_196159 100723851705403260710387 := by
  unfold tailWord_196159
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154506496356919135135531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4769670997571279423423687 7154506496356919135135531)
  ·
    refine ⟨10731759744535378702703297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7154506496356919135135531 10731759744535378702703297)
    ·
      refine ⟨8048819808401534027027473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10731759744535378702703297 8048819808401534027027473)
      ·
        refine ⟨6036614856301150520270605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8048819808401534027027473 6036614856301150520270605)
        ·
          refine ⟨2263730571112931445101477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6036614856301150520270605 2263730571112931445101477)
          ·
            refine ⟨424449482083674645956527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2263730571112931445101477 424449482083674645956527)
            ·
              refine ⟨636674223125511968934791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424449482083674645956527 636674223125511968934791)
              ·
                refine ⟨955011334688267953402187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636674223125511968934791 955011334688267953402187)
                ·
                  refine ⟨1432517002032401930103281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955011334688267953402187 1432517002032401930103281)
                  ·
                    refine ⟨1074387751524301447577461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1432517002032401930103281 1074387751524301447577461)
                    ·
                      refine ⟨100723851705403260710387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1074387751524301447577461 100723851705403260710387)
                      ·
                        rfl

theorem cell23_196159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_196159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196159 prefixEnd_196159 := by exact prefixLift 196159
  have htrace : WordTrace (prefixWord ++ tailWord_196159) baseStart_196159 baseEnd_196159 := by
    simpa [prefixWord, tailWord_196159, baseEnd_196159] using wordTrace_append hprefix tailTrace_196159
  have hstable : (prefixWord ++ tailWord_196159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196159).length < 2 ^ (prefixWord ++ tailWord_196159).sum := by decide
  have hdescent : baseEnd_196159 < baseStart_196159 := by decide
  rcases family_descends (prefixWord ++ tailWord_196159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196313 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 3]
def baseStart_196313 : Nat := 118140960795 + 196313 * 2 ^ 59
def prefixEnd_196313 : Nat := 4983230072969 + 3 ^ 40 * 196313 * 2
def baseEnd_196313 : Nat := 100802927726195658184679

theorem tailTrace_196313 : CollatzResearch.WordTrace tailWord_196313 prefixEnd_196313 100802927726195658184679 := by
  unfold tailWord_196313
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160123337799003436241593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4773415558532668957494395 7160123337799003436241593)
  ·
    refine ⟨5370092503349252577181195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7160123337799003436241593 5370092503349252577181195)
    ·
      refine ⟨8055138755023878865771793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5370092503349252577181195 8055138755023878865771793)
      ·
        refine ⟨6041354066267909149328845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8055138755023878865771793 6041354066267909149328845)
        ·
          refine ⟨2265507774850465930998317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6041354066267909149328845 2265507774850465930998317)
          ·
            refine ⟨849565415568924724124369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2265507774850465930998317 849565415568924724124369)
            ·
              refine ⟨637174061676693543093277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849565415568924724124369 637174061676693543093277)
              ·
                refine ⟨238940273128760078659979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637174061676693543093277 238940273128760078659979)
                ·
                  refine ⟨358410409693140117989969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238940273128760078659979 358410409693140117989969)
                  ·
                    refine ⟨268807807269855088492477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 358410409693140117989969 268807807269855088492477)
                    ·
                      refine ⟨100802927726195658184679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 268807807269855088492477 100802927726195658184679)
                      ·
                        rfl

theorem cell23_196313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_196313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196313 prefixEnd_196313 := by exact prefixLift 196313
  have htrace : WordTrace (prefixWord ++ tailWord_196313) baseStart_196313 baseEnd_196313 := by
    simpa [prefixWord, tailWord_196313, baseEnd_196313] using wordTrace_append hprefix tailTrace_196313
  have hstable : (prefixWord ++ tailWord_196313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196313).length < 2 ^ (prefixWord ++ tailWord_196313).sum := by decide
  have hdescent : baseEnd_196313 < baseStart_196313 := by decide
  rcases family_descends (prefixWord ++ tailWord_196313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196329 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 2, 7]
def baseStart_196329 : Nat := 118140960795 + 196329 * 2 ^ 59
def prefixEnd_196329 : Nat := 4983230072969 + 3 ^ 40 * 196329 * 2
def baseEnd_196329 : Nat := 33603714472222531861535

theorem tailTrace_196329 : CollatzResearch.WordTrace tailWord_196329 prefixEnd_196329 33603714472222531861535 := by
  unfold tailWord_196329
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160706905741038168824041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4773804603827358779216027 7160706905741038168824041)
  ·
    refine ⟨5370530179305778626618031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7160706905741038168824041 5370530179305778626618031)
    ·
      refine ⟨8055795268958667939927047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5370530179305778626618031 8055795268958667939927047)
      ·
        refine ⟨12083692903438001909890571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8055795268958667939927047 12083692903438001909890571)
        ·
          refine ⟨18125539355157002864835857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12083692903438001909890571 18125539355157002864835857)
          ·
            refine ⟨13594154516367752148626893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18125539355157002864835857 13594154516367752148626893)
            ·
              refine ⟨5097807943637907055735085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13594154516367752148626893 5097807943637907055735085)
              ·
                refine ⟨1911677978864215145900657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5097807943637907055735085 1911677978864215145900657)
                ·
                  refine ⟨1433758484148161359425493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1911677978864215145900657 1433758484148161359425493)
                  ·
                    refine ⟨33603714472222531861535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1433758484148161359425493 33603714472222531861535)
                    ·
                      rfl

theorem cell23_196329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_196329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196329 prefixEnd_196329 := by exact prefixLift 196329
  have htrace : WordTrace (prefixWord ++ tailWord_196329) baseStart_196329 baseEnd_196329 := by
    simpa [prefixWord, tailWord_196329, baseEnd_196329] using wordTrace_append hprefix tailTrace_196329
  have hstable : (prefixWord ++ tailWord_196329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196329).length < 2 ^ (prefixWord ++ tailWord_196329).sum := by decide
  have hdescent : baseEnd_196329 < baseStart_196329 := by decide
  rcases family_descends (prefixWord ++ tailWord_196329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196340 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_196340 : Nat := 118140960795 + 196340 * 2 ^ 59
def prefixEnd_196340 : Nat := 4983230072969 + 3 ^ 40 * 196340 * 2
def baseEnd_196340 : Nat := 100816791703867052547055

theorem tailTrace_196340 : CollatzResearch.WordTrace tailWord_196340 prefixEnd_196340 100816791703867052547055 := by
  unfold tailWord_196340
  simp only [CollatzResearch.WordTrace]
  refine ⟨3580554054350593523737237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4774072072467458031649649 3580554054350593523737237)
  ·
    refine ⟨167838471297684071425183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3580554054350593523737237 167838471297684071425183)
    ·
      refine ⟨251757706946526107137775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167838471297684071425183 251757706946526107137775)
      ·
        refine ⟨377636560419789160706663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251757706946526107137775 377636560419789160706663)
        ·
          refine ⟨566454840629683741059995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377636560419789160706663 566454840629683741059995)
          ·
            refine ⟨849682260944525611589993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566454840629683741059995 849682260944525611589993)
            ·
              refine ⟨637261695708394208692495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849682260944525611589993 637261695708394208692495)
              ·
                refine ⟨955892543562591313038743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637261695708394208692495 955892543562591313038743)
                ·
                  refine ⟨1433838815343886969558115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955892543562591313038743 1433838815343886969558115)
                  ·
                    refine ⟨2150758223015830454337173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1433838815343886969558115 2150758223015830454337173)
                    ·
                      refine ⟨100816791703867052547055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2150758223015830454337173 100816791703867052547055)
                      ·
                        rfl

theorem cell23_196340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_196340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196340 prefixEnd_196340 := by exact prefixLift 196340
  have htrace : WordTrace (prefixWord ++ tailWord_196340) baseStart_196340 baseEnd_196340 := by
    simpa [prefixWord, tailWord_196340, baseEnd_196340] using wordTrace_append hprefix tailTrace_196340
  have hstable : (prefixWord ++ tailWord_196340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196340).length < 2 ^ (prefixWord ++ tailWord_196340).sum := by decide
  have hdescent : baseEnd_196340 < baseStart_196340 := by decide
  rcases family_descends (prefixWord ++ tailWord_196340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196358 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_196358 : Nat := 118140960795 + 196358 * 2 ^ 59
def prefixEnd_196358 : Nat := 4983230072969 + 3 ^ 40 * 196358 * 2
def baseEnd_196358 : Nat := 33608678118549327373991

theorem tailTrace_196358 : CollatzResearch.WordTrace tailWord_196358 prefixEnd_196358 33608678118549327373991 := by
  unfold tailWord_196358
  simp only [CollatzResearch.WordTrace]
  refine ⟨223805144457374253800929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4774509748423984081086485 223805144457374253800929)
  ·
    refine ⟨167853858343030690350697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223805144457374253800929 167853858343030690350697)
    ·
      refine ⟨125890393757273017763023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167853858343030690350697 125890393757273017763023)
      ·
        refine ⟨188835590635909526644535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125890393757273017763023 188835590635909526644535)
        ·
          refine ⟨283253385953864289966803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188835590635909526644535 283253385953864289966803)
          ·
            refine ⟨424880078930796434950205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283253385953864289966803 424880078930796434950205)
            ·
              refine ⟨159330029599048663106327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424880078930796434950205 159330029599048663106327)
              ·
                refine ⟨238995044398572994659491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159330029599048663106327 238995044398572994659491)
                ·
                  refine ⟨358492566597859491989237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238995044398572994659491 358492566597859491989237)
                  ·
                    refine ⟨33608678118549327373991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 358492566597859491989237 33608678118549327373991)
                    ·
                      rfl

theorem cell23_196358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_196358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196358 prefixEnd_196358 := by exact prefixLift 196358
  have htrace : WordTrace (prefixWord ++ tailWord_196358) baseStart_196358 baseEnd_196358 := by
    simpa [prefixWord, tailWord_196358, baseEnd_196358] using wordTrace_append hprefix tailTrace_196358
  have hstable : (prefixWord ++ tailWord_196358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196358).length < 2 ^ (prefixWord ++ tailWord_196358).sum := by decide
  have hdescent : baseEnd_196358 < baseStart_196358 := by decide
  rcases family_descends (prefixWord ++ tailWord_196358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196383 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 3, 4, 2]
def baseStart_196383 : Nat := 118140960795 + 196383 * 2 ^ 59
def prefixEnd_196383 : Nat := 4983230072969 + 3 ^ 40 * 196383 * 2
def baseEnd_196383 : Nat := 100838871372010384309357

theorem tailTrace_196383 : CollatzResearch.WordTrace tailWord_196383 prefixEnd_196383 100838871372010384309357 := by
  unfold tailWord_196383
  simp only [CollatzResearch.WordTrace]
  refine ⟨7162676447545405391289803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4775117631696936927526535 7162676447545405391289803)
  ·
    refine ⟨10744014671318108086934705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7162676447545405391289803 10744014671318108086934705)
    ·
      refine ⟨8058011003488581065201029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10744014671318108086934705 8058011003488581065201029)
      ·
        refine ⟨1510877063154108949725193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8058011003488581065201029 1510877063154108949725193)
        ·
          refine ⟨1133157797365581712293895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1510877063154108949725193 1133157797365581712293895)
          ·
            refine ⟨1699736696048372568440843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133157797365581712293895 1699736696048372568440843)
            ·
              refine ⟨2549605044072558852661265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699736696048372568440843 2549605044072558852661265)
              ·
                refine ⟨1912203783054419139495949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549605044072558852661265 1912203783054419139495949)
                ·
                  refine ⟨717076418645407177310981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1912203783054419139495949 717076418645407177310981)
                  ·
                    refine ⟨134451828496013845745809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 717076418645407177310981 134451828496013845745809)
                    ·
                      refine ⟨100838871372010384309357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134451828496013845745809 100838871372010384309357)
                      ·
                        rfl

theorem cell23_196383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_196383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196383 prefixEnd_196383 := by exact prefixLift 196383
  have htrace : WordTrace (prefixWord ++ tailWord_196383) baseStart_196383 baseEnd_196383 := by
    simpa [prefixWord, tailWord_196383, baseEnd_196383] using wordTrace_append hprefix tailTrace_196383
  have hstable : (prefixWord ++ tailWord_196383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196383).length < 2 ^ (prefixWord ++ tailWord_196383).sum := by decide
  have hdescent : baseEnd_196383 < baseStart_196383 := by decide
  rcases family_descends (prefixWord ++ tailWord_196383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196396 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_196396 : Nat := 118140960795 + 196396 * 2 ^ 59
def prefixEnd_196396 : Nat := 4983230072969 + 3 ^ 40 * 196396 * 2
def baseEnd_196396 : Nat := 100845546620518833446797

theorem tailTrace_196396 : CollatzResearch.WordTrace tailWord_196396 prefixEnd_196396 100845546620518833446797 := by
  unfold tailWord_196396
  simp only [CollatzResearch.WordTrace]
  refine ⟨3581575298249154305756521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4775433730998872407675361 3581575298249154305756521)
  ·
    refine ⟨2686181473686865729317391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3581575298249154305756521 2686181473686865729317391)
    ·
      refine ⟨4029272210530298593976087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686181473686865729317391 4029272210530298593976087)
      ·
        refine ⟨6043908315795447890964131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029272210530298593976087 6043908315795447890964131)
        ·
          refine ⟨9065862473693171836446197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6043908315795447890964131 9065862473693171836446197)
          ·
            refine ⟨849924606908734859666831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9065862473693171836446197 849924606908734859666831)
            ·
              refine ⟨1274886910363102289500247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849924606908734859666831 1274886910363102289500247)
              ·
                refine ⟨1912330365544653434250371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274886910363102289500247 1912330365544653434250371)
                ·
                  refine ⟨2868495548316980151375557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912330365544653434250371 2868495548316980151375557)
                  ·
                    refine ⟨537842915309433778382917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2868495548316980151375557 537842915309433778382917)
                    ·
                      refine ⟨100845546620518833446797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 537842915309433778382917 100845546620518833446797)
                      ·
                        rfl

theorem cell23_196396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_196396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196396 prefixEnd_196396 := by exact prefixLift 196396
  have htrace : WordTrace (prefixWord ++ tailWord_196396) baseStart_196396 baseEnd_196396 := by
    simpa [prefixWord, tailWord_196396, baseEnd_196396] using wordTrace_append hprefix tailTrace_196396
  have hstable : (prefixWord ++ tailWord_196396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196396).length < 2 ^ (prefixWord ++ tailWord_196396).sum := by decide
  have hdescent : baseEnd_196396 < baseStart_196396 := by decide
  rcases family_descends (prefixWord ++ tailWord_196396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196423 : List Nat := [1, 1, 4, 1, 2, 1, 3, 5, 5]
def baseStart_196423 : Nat := 118140960795 + 196423 * 2 ^ 59
def prefixEnd_196423 : Nat := 4983230072969 + 3 ^ 40 * 196423 * 2
def baseEnd_196423 : Nat := 11206601177576691978797

theorem tailTrace_196423 : CollatzResearch.WordTrace tailWord_196423 prefixEnd_196423 11206601177576691978797 := by
  unfold tailWord_196423
  simp only [CollatzResearch.WordTrace]
  refine ⟨7164135367400492222745923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4776090244933661481830615 7164135367400492222745923)
  ·
    refine ⟨10746203051100738334118885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7164135367400492222745923 10746203051100738334118885)
    ·
      refine ⟨2014913072081388437647291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10746203051100738334118885 2014913072081388437647291)
      ·
        refine ⟨3022369608122082656470937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2014913072081388437647291 3022369608122082656470937)
        ·
          refine ⟨2266777206091561992353203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3022369608122082656470937 2266777206091561992353203)
          ·
            refine ⟨3400165809137342988529805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266777206091561992353203 3400165809137342988529805)
            ·
              refine ⟨1275062178426503620698677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3400165809137342988529805 1275062178426503620698677)
              ·
                refine ⟨119537079227484714440501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1275062178426503620698677 119537079227484714440501)
                ·
                  refine ⟨11206601177576691978797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119537079227484714440501 11206601177576691978797)
                  ·
                    rfl

theorem cell23_196423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 5].length) (baseStart_196423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196423 prefixEnd_196423 := by exact prefixLift 196423
  have htrace : WordTrace (prefixWord ++ tailWord_196423) baseStart_196423 baseEnd_196423 := by
    simpa [prefixWord, tailWord_196423, baseEnd_196423] using wordTrace_append hprefix tailTrace_196423
  have hstable : (prefixWord ++ tailWord_196423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196423).length < 2 ^ (prefixWord ++ tailWord_196423).sum := by decide
  have hdescent : baseEnd_196423 < baseStart_196423 := by decide
  rcases family_descends (prefixWord ++ tailWord_196423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196433 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_196433 : Nat := 118140960795 + 196433 * 2 ^ 59
def prefixEnd_196433 : Nat := 4983230072969 + 3 ^ 40 * 196433 * 2
def baseEnd_196433 : Nat := 100864545404735188684127

theorem tailTrace_196433 : CollatzResearch.WordTrace tailWord_196433 prefixEnd_196433 100864545404735188684127 := by
  unfold tailWord_196433
  simp only [CollatzResearch.WordTrace]
  refine ⟨7164500097364263930609953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4776333398242842620406635 7164500097364263930609953)
  ·
    refine ⟨5373375073023197947957465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7164500097364263930609953 5373375073023197947957465)
    ·
      refine ⟨4030031304767398460968099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5373375073023197947957465 4030031304767398460968099)
      ·
        refine ⟨6045046957151097691452149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030031304767398460968099 6045046957151097691452149)
        ·
          refine ⟨566723152232915408573639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6045046957151097691452149 566723152232915408573639)
          ·
            refine ⟨850084728349373112860459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566723152232915408573639 850084728349373112860459)
            ·
              refine ⟨1275127092524059669290689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850084728349373112860459 1275127092524059669290689)
              ·
                refine ⟨956345319393044751968017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275127092524059669290689 956345319393044751968017)
                ·
                  refine ⟨717258989544783563976013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 956345319393044751968017 717258989544783563976013)
                  ·
                    refine ⟨268972121079293836491005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717258989544783563976013 268972121079293836491005)
                    ·
                      refine ⟨100864545404735188684127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 268972121079293836491005 100864545404735188684127)
                      ·
                        rfl

theorem cell23_196433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_196433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196433 prefixEnd_196433 := by exact prefixLift 196433
  have htrace : WordTrace (prefixWord ++ tailWord_196433) baseStart_196433 baseEnd_196433 := by
    simpa [prefixWord, tailWord_196433, baseEnd_196433] using wordTrace_append hprefix tailTrace_196433
  have hstable : (prefixWord ++ tailWord_196433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196433).length < 2 ^ (prefixWord ++ tailWord_196433).sum := by decide
  have hdescent : baseEnd_196433 < baseStart_196433 := by decide
  rcases family_descends (prefixWord ++ tailWord_196433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196434 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_196434 : Nat := 118140960795 + 196434 * 2 ^ 59
def prefixEnd_196434 : Nat := 4983230072969 + 3 ^ 40 * 196434 * 2
def baseEnd_196434 : Nat := 100865058885389684771623

theorem tailTrace_196434 : CollatzResearch.WordTrace tailWord_196434 prefixEnd_196434 100865058885389684771623 := by
  unfold tailWord_196434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791134142590160275349089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4776357713573760734264237 1791134142590160275349089)
  ·
    refine ⟨1343350606942620206511817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1791134142590160275349089 1343350606942620206511817)
    ·
      refine ⟨1007512955206965154883863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1343350606942620206511817 1007512955206965154883863)
      ·
        refine ⟨1511269432810447732325795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007512955206965154883863 1511269432810447732325795)
        ·
          refine ⟨2266904149215671598488693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511269432810447732325795 2266904149215671598488693)
          ·
            refine ⟨212522263988969212358315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2266904149215671598488693 212522263988969212358315)
            ·
              refine ⟨318783395983453818537473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212522263988969212358315 318783395983453818537473)
              ·
                refine ⟨239087546987590363903105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318783395983453818537473 239087546987590363903105)
                ·
                  refine ⟨179315660240692772927329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239087546987590363903105 179315660240692772927329)
                  ·
                    refine ⟨134486745180519579695497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 179315660240692772927329 134486745180519579695497)
                    ·
                      refine ⟨100865058885389684771623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134486745180519579695497 100865058885389684771623)
                      ·
                        rfl

theorem cell23_196434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_196434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196434 prefixEnd_196434 := by exact prefixLift 196434
  have htrace : WordTrace (prefixWord ++ tailWord_196434) baseStart_196434 baseEnd_196434 := by
    simpa [prefixWord, tailWord_196434, baseEnd_196434] using wordTrace_append hprefix tailTrace_196434
  have hstable : (prefixWord ++ tailWord_196434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196434).length < 2 ^ (prefixWord ++ tailWord_196434).sum := by decide
  have hdescent : baseEnd_196434 < baseStart_196434 := by decide
  rcases family_descends (prefixWord ++ tailWord_196434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196450 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_196450 : Nat := 118140960795 + 196450 * 2 ^ 59
def prefixEnd_196450 : Nat := 4983230072969 + 3 ^ 40 * 196450 * 2
def baseEnd_196450 : Nat := 100873274575861622171549

theorem tailTrace_196450 : CollatzResearch.WordTrace tailWord_196450 prefixEnd_196450 100873274575861622171549 := by
  unfold tailWord_196450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791280034575668958494701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4776746758868450555985869 1791280034575668958494701)
  ·
    refine ⟨671730012965875859435513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1791280034575668958494701 671730012965875859435513)
    ·
      refine ⟨503797509724406894576635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 671730012965875859435513 503797509724406894576635)
      ·
        refine ⟨755696264586610341864953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503797509724406894576635 755696264586610341864953)
        ·
          refine ⟨566772198439957756398715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755696264586610341864953 566772198439957756398715)
          ·
            refine ⟨850158297659936634598073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566772198439957756398715 850158297659936634598073)
            ·
              refine ⟨637618723244952475948555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850158297659936634598073 637618723244952475948555)
              ·
                refine ⟨956428084867428713922833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637618723244952475948555 956428084867428713922833)
                ·
                  refine ⟨717321063650571535442125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 956428084867428713922833 717321063650571535442125)
                  ·
                    refine ⟨268995398868964325790797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717321063650571535442125 268995398868964325790797)
                    ·
                      refine ⟨100873274575861622171549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 268995398868964325790797 100873274575861622171549)
                      ·
                        rfl

theorem cell23_196450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_196450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196450 prefixEnd_196450 := by exact prefixLift 196450
  have htrace : WordTrace (prefixWord ++ tailWord_196450) baseStart_196450 baseEnd_196450 := by
    simpa [prefixWord, tailWord_196450, baseEnd_196450] using wordTrace_append hprefix tailTrace_196450
  have hstable : (prefixWord ++ tailWord_196450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196450).length < 2 ^ (prefixWord ++ tailWord_196450).sum := by decide
  have hdescent : baseEnd_196450 < baseStart_196450 := by decide
  rcases family_descends (prefixWord ++ tailWord_196450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196466 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_196466 : Nat := 118140960795 + 196466 * 2 ^ 59
def prefixEnd_196466 : Nat := 4983230072969 + 3 ^ 40 * 196466 * 2
def baseEnd_196466 : Nat := 33627163422111186523825

theorem tailTrace_196466 : CollatzResearch.WordTrace tailWord_196466 prefixEnd_196466 33627163422111186523825 := by
  unfold tailWord_196466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791425926561177641640313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4777135804163140377707501 1791425926561177641640313)
  ·
    refine ⟨1343569444920883231230235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1791425926561177641640313 1343569444920883231230235)
    ·
      refine ⟨2015354167381324846845353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343569444920883231230235 2015354167381324846845353)
      ·
        refine ⟨1511515625535993635134015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2015354167381324846845353 1511515625535993635134015)
        ·
          refine ⟨2267273438303990452701023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511515625535993635134015 2267273438303990452701023)
          ·
            refine ⟨3400910157455985679051535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267273438303990452701023 3400910157455985679051535)
            ·
              refine ⟨5101365236183978518577303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400910157455985679051535 5101365236183978518577303)
              ·
                refine ⟨7652047854275967777865955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5101365236183978518577303 7652047854275967777865955)
                ·
                  refine ⟨11478071781413951666798933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7652047854275967777865955 11478071781413951666798933)
                  ·
                    refine ⟨33627163422111186523825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 11478071781413951666798933 33627163422111186523825)
                    ·
                      rfl

theorem cell23_196466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_196466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196466 prefixEnd_196466 := by exact prefixLift 196466
  have htrace : WordTrace (prefixWord ++ tailWord_196466) baseStart_196466 baseEnd_196466 := by
    simpa [prefixWord, tailWord_196466, baseEnd_196466] using wordTrace_append hprefix tailTrace_196466
  have hstable : (prefixWord ++ tailWord_196466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196466).length < 2 ^ (prefixWord ++ tailWord_196466).sum := by decide
  have hdescent : baseEnd_196466 < baseStart_196466 := by decide
  rcases family_descends (prefixWord ++ tailWord_196466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196473 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_196473 : Nat := 118140960795 + 196473 * 2 ^ 59
def prefixEnd_196473 : Nat := 4983230072969 + 3 ^ 40 * 196473 * 2
def baseEnd_196473 : Nat := 100885084630915032183943

theorem tailTrace_196473 : CollatzResearch.WordTrace tailWord_196473 prefixEnd_196473 100885084630915032183943 := by
  unfold tailWord_196473
  simp only [CollatzResearch.WordTrace]
  refine ⟨7165959017219350762066073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4777306011479567174710715 7165959017219350762066073)
  ·
    refine ⟨5374469262914513071549555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7165959017219350762066073 5374469262914513071549555)
    ·
      refine ⟨8061703894371769607324333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5374469262914513071549555 8061703894371769607324333)
      ·
        refine ⟨3023138960389413602746625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8061703894371769607324333 3023138960389413602746625)
        ·
          refine ⟨2267354220292060202059969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3023138960389413602746625 2267354220292060202059969)
          ·
            refine ⟨1700515665219045151544977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2267354220292060202059969 1700515665219045151544977)
            ·
              refine ⟨1275386748914283863658733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1700515665219045151544977 1275386748914283863658733)
              ·
                refine ⟨478270030842856448872025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1275386748914283863658733 478270030842856448872025)
                ·
                  refine ⟨358702523132142336654019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478270030842856448872025 358702523132142336654019)
                  ·
                    refine ⟨538053784698213504981029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 358702523132142336654019 538053784698213504981029)
                    ·
                      refine ⟨100885084630915032183943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 538053784698213504981029 100885084630915032183943)
                      ·
                        rfl

theorem cell23_196473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_196473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196473 prefixEnd_196473 := by exact prefixLift 196473
  have htrace : WordTrace (prefixWord ++ tailWord_196473) baseStart_196473 baseEnd_196473 := by
    simpa [prefixWord, tailWord_196473, baseEnd_196473] using wordTrace_append hprefix tailTrace_196473
  have hstable : (prefixWord ++ tailWord_196473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196473).length < 2 ^ (prefixWord ++ tailWord_196473).sum := by decide
  have hdescent : baseEnd_196473 < baseStart_196473 := by decide
  rcases family_descends (prefixWord ++ tailWord_196473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196476 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_196476 : Nat := 118140960795 + 196476 * 2 ^ 59
def prefixEnd_196476 : Nat := 4983230072969 + 3 ^ 40 * 196476 * 2
def baseEnd_196476 : Nat := 100886625072878520446429

theorem tailTrace_196476 : CollatzResearch.WordTrace tailWord_196476 prefixEnd_196476 100886625072878520446429 := by
  unfold tailWord_196476
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583034218104241137212641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4777378957472321516283521 3583034218104241137212641)
  ·
    refine ⟨2687275663578180852909481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3583034218104241137212641 2687275663578180852909481)
    ·
      refine ⟨2015456747683635639682111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2687275663578180852909481 2015456747683635639682111)
      ·
        refine ⟨3023185121525453459523167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015456747683635639682111 3023185121525453459523167)
        ·
          refine ⟨4534777682288180189284751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023185121525453459523167 4534777682288180189284751)
          ·
            refine ⟨6802166523432270283927127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534777682288180189284751 6802166523432270283927127)
            ·
              refine ⟨10203249785148405425890691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6802166523432270283927127 10203249785148405425890691)
              ·
                refine ⟨15304874677722608138836037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10203249785148405425890691 15304874677722608138836037)
                ·
                  refine ⟨2869664002072989026031757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15304874677722608138836037 2869664002072989026031757)
                  ·
                    refine ⟨1076124000777370884761909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2869664002072989026031757 1076124000777370884761909)
                    ·
                      refine ⟨100886625072878520446429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1076124000777370884761909 100886625072878520446429)
                      ·
                        rfl

theorem cell23_196476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_196476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196476 prefixEnd_196476 := by exact prefixLift 196476
  have htrace : WordTrace (prefixWord ++ tailWord_196476) baseStart_196476 baseEnd_196476 := by
    simpa [prefixWord, tailWord_196476, baseEnd_196476] using wordTrace_append hprefix tailTrace_196476
  have hstable : (prefixWord ++ tailWord_196476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196476).length < 2 ^ (prefixWord ++ tailWord_196476).sum := by decide
  have hdescent : baseEnd_196476 < baseStart_196476 := by decide
  rcases family_descends (prefixWord ++ tailWord_196476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196502 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_196502 : Nat := 118140960795 + 196502 * 2 ^ 59
def prefixEnd_196502 : Nat := 4983230072969 + 3 ^ 40 * 196502 * 2
def baseEnd_196502 : Nat := 100899975569895418721311

theorem tailTrace_196502 : CollatzResearch.WordTrace tailWord_196502 prefixEnd_196502 100899975569895418721311 := by
  unfold tailWord_196502
  simp only [CollatzResearch.WordTrace]
  refine ⟨447938545882143044679485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4778011156076192476581173 447938545882143044679485)
  ·
    refine ⟨167976954705803641754807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 447938545882143044679485 167976954705803641754807)
    ·
      refine ⟨251965432058705462632211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167976954705803641754807 251965432058705462632211)
      ·
        refine ⟨377948148088058193948317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251965432058705462632211 377948148088058193948317)
        ·
          refine ⟨141730555533021822730619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377948148088058193948317 141730555533021822730619)
          ·
            refine ⟨212595833299532734095929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141730555533021822730619 212595833299532734095929)
            ·
              refine ⟨159446874974649550571947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212595833299532734095929 159446874974649550571947)
              ·
                refine ⟨239170312461974325857921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159446874974649550571947 239170312461974325857921)
                ·
                  refine ⟨179377734346480744393441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239170312461974325857921 179377734346480744393441)
                  ·
                    refine ⟨134533300759860558295081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 179377734346480744393441 134533300759860558295081)
                    ·
                      refine ⟨100899975569895418721311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134533300759860558295081 100899975569895418721311)
                      ·
                        rfl

theorem cell23_196502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_196502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196502 prefixEnd_196502 := by exact prefixLift 196502
  have htrace : WordTrace (prefixWord ++ tailWord_196502) baseStart_196502 baseEnd_196502 := by
    simpa [prefixWord, tailWord_196502, baseEnd_196502] using wordTrace_append hprefix tailTrace_196502
  have hstable : (prefixWord ++ tailWord_196502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196502).length < 2 ^ (prefixWord ++ tailWord_196502).sum := by decide
  have hdescent : baseEnd_196502 < baseStart_196502 := by decide
  rcases family_descends (prefixWord ++ tailWord_196502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196580 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_196580 : Nat := 118140960795 + 196580 * 2 ^ 59
def prefixEnd_196580 : Nat := 4983230072969 + 3 ^ 40 * 196580 * 2
def baseEnd_196580 : Nat := 100940027060946113545951

theorem tailTrace_196580 : CollatzResearch.WordTrace tailWord_196580 prefixEnd_196580 100940027060946113545951 := by
  unfold tailWord_196580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3584930813915854018105597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4779907751887805357474129 3584930813915854018105597)
  ·
    refine ⟨1344349055218445256789599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3584930813915854018105597 1344349055218445256789599)
    ·
      refine ⟨2016523582827667885184399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1344349055218445256789599 2016523582827667885184399)
      ·
        refine ⟨3024785374241501827776599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016523582827667885184399 3024785374241501827776599)
        ·
          refine ⟨4537178061362252741664899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024785374241501827776599 4537178061362252741664899)
          ·
            refine ⟨6805767092043379112497349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537178061362252741664899 6805767092043379112497349)
            ·
              refine ⟨1276081329758133583593253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6805767092043379112497349 1276081329758133583593253)
              ·
                refine ⟨239265249329650046923735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1276081329758133583593253 239265249329650046923735)
                ·
                  refine ⟨358897873994475070385603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239265249329650046923735 358897873994475070385603)
                  ·
                    refine ⟨538346810991712605578405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 358897873994475070385603 538346810991712605578405)
                    ·
                      refine ⟨100940027060946113545951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 538346810991712605578405 100940027060946113545951)
                      ·
                        rfl

theorem cell23_196580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_196580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196580 prefixEnd_196580 := by exact prefixLift 196580
  have htrace : WordTrace (prefixWord ++ tailWord_196580) baseStart_196580 baseEnd_196580 := by
    simpa [prefixWord, tailWord_196580, baseEnd_196580] using wordTrace_append hprefix tailTrace_196580
  have hstable : (prefixWord ++ tailWord_196580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196580).length < 2 ^ (prefixWord ++ tailWord_196580).sum := by decide
  have hdescent : baseEnd_196580 < baseStart_196580 := by decide
  rcases family_descends (prefixWord ++ tailWord_196580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196590 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_196590 : Nat := 118140960795 + 196590 * 2 ^ 59
def prefixEnd_196590 : Nat := 4983230072969 + 3 ^ 40 * 196590 * 2
def baseEnd_196590 : Nat := 33648387289163691473635

theorem tailTrace_196590 : CollatzResearch.WordTrace tailWord_196590 prefixEnd_196590 33648387289163691473635 := by
  unfold tailWord_196590
  simp only [CollatzResearch.WordTrace]
  refine ⟨896278294724434968009403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4780150905196986496050149 896278294724434968009403)
  ·
    refine ⟨1344417442086652452014105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 896278294724434968009403 1344417442086652452014105)
    ·
      refine ⟨1008313081564989339010579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1344417442086652452014105 1008313081564989339010579)
      ·
        refine ⟨1512469622347484008515869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008313081564989339010579 1512469622347484008515869)
        ·
          refine ⟨567176108380306503193451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1512469622347484008515869 567176108380306503193451)
          ·
            refine ⟨850764162570459754790177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567176108380306503193451 850764162570459754790177)
            ·
              refine ⟨638073121927844816092633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850764162570459754790177 638073121927844816092633)
              ·
                refine ⟨478554841445883612069475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638073121927844816092633 478554841445883612069475)
                ·
                  refine ⟨717832262168825418104213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478554841445883612069475 717832262168825418104213)
                  ·
                    refine ⟨33648387289163691473635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 717832262168825418104213 33648387289163691473635)
                    ·
                      rfl

theorem cell23_196590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_196590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196590 prefixEnd_196590 := by exact prefixLift 196590
  have htrace : WordTrace (prefixWord ++ tailWord_196590) baseStart_196590 baseEnd_196590 := by
    simpa [prefixWord, tailWord_196590, baseEnd_196590] using wordTrace_append hprefix tailTrace_196590
  have hstable : (prefixWord ++ tailWord_196590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196590).length < 2 ^ (prefixWord ++ tailWord_196590).sum := by decide
  have hdescent : baseEnd_196590 < baseStart_196590 := by decide
  rcases family_descends (prefixWord ++ tailWord_196590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196637 : List Nat := [1, 4, 2, 2, 2, 3, 2, 7]
def baseStart_196637 : Nat := 118140960795 + 196637 * 2 ^ 59
def prefixEnd_196637 : Nat := 4983230072969 + 3 ^ 40 * 196637 * 2
def baseEnd_196637 : Nat := 3739603535490829279007

theorem tailTrace_196637 : CollatzResearch.WordTrace tailWord_196637 prefixEnd_196637 3739603535490829279007 := by
  unfold tailWord_196637
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171940588625206771036165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4781293725750137847357443 7171940588625206771036165)
  ·
    refine ⟨1344738860367226269569281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7171940588625206771036165 1344738860367226269569281)
    ·
      refine ⟨1008554145275419702176961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1344738860367226269569281 1008554145275419702176961)
      ·
        refine ⟨756415608956564776632721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1008554145275419702176961 756415608956564776632721)
        ·
          refine ⟨567311706717423582474541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756415608956564776632721 567311706717423582474541)
          ·
            refine ⟨212741890019033843427953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 567311706717423582474541 212741890019033843427953)
            ·
              refine ⟨159556417514275382570965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212741890019033843427953 159556417514275382570965)
              ·
                refine ⟨3739603535490829279007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159556417514275382570965 3739603535490829279007)
                ·
                  rfl

theorem cell23_196637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 7].length) (baseStart_196637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196637 prefixEnd_196637 := by exact prefixLift 196637
  have htrace : WordTrace (prefixWord ++ tailWord_196637) baseStart_196637 baseEnd_196637 := by
    simpa [prefixWord, tailWord_196637, baseEnd_196637] using wordTrace_append hprefix tailTrace_196637
  have hstable : (prefixWord ++ tailWord_196637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196637).length < 2 ^ (prefixWord ++ tailWord_196637).sum := by decide
  have hdescent : baseEnd_196637 < baseStart_196637 := by decide
  rcases family_descends (prefixWord ++ tailWord_196637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196643 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 5]
def baseStart_196643 : Nat := 118140960795 + 196643 * 2 ^ 59
def prefixEnd_196643 : Nat := 4983230072969 + 3 ^ 40 * 196643 * 2
def baseEnd_196643 : Nat := 100972376342179367058161

theorem tailTrace_196643 : CollatzResearch.WordTrace tailWord_196643 prefixEnd_196643 100972376342179367058161 := by
  unfold tailWord_196643
  simp only [CollatzResearch.WordTrace]
  refine ⟨7172159426603469795754583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4781439617735646530503055 7172159426603469795754583)
  ·
    refine ⟨10758239139905204693631875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7172159426603469795754583 10758239139905204693631875)
    ·
      refine ⟨16137358709857807040447813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10758239139905204693631875 16137358709857807040447813)
      ·
        refine ⟨3025754758098338820083965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16137358709857807040447813 3025754758098338820083965)
        ·
          refine ⟨1134658034286877057531487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3025754758098338820083965 1134658034286877057531487)
          ·
            refine ⟨1701987051430315586297231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134658034286877057531487 1701987051430315586297231)
            ·
              refine ⟨2552980577145473379445847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1701987051430315586297231 2552980577145473379445847)
              ·
                refine ⟨3829470865718210069168771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552980577145473379445847 3829470865718210069168771)
                ·
                  refine ⟨5744206298577315103753157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829470865718210069168771 5744206298577315103753157)
                  ·
                    refine ⟨1077038680983246581953717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744206298577315103753157 1077038680983246581953717)
                    ·
                      refine ⟨100972376342179367058161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1077038680983246581953717 100972376342179367058161)
                      ·
                        rfl

theorem cell23_196643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_196643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196643 prefixEnd_196643 := by exact prefixLift 196643
  have htrace : WordTrace (prefixWord ++ tailWord_196643) baseStart_196643 baseEnd_196643 := by
    simpa [prefixWord, tailWord_196643, baseEnd_196643] using wordTrace_append hprefix tailTrace_196643
  have hstable : (prefixWord ++ tailWord_196643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196643).length < 2 ^ (prefixWord ++ tailWord_196643).sum := by decide
  have hdescent : baseEnd_196643 < baseStart_196643 := by decide
  rcases family_descends (prefixWord ++ tailWord_196643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196663 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 4, 6]
def baseStart_196663 : Nat := 118140960795 + 196663 * 2 ^ 59
def prefixEnd_196663 : Nat := 4983230072969 + 3 ^ 40 * 196663 * 2
def baseEnd_196663 : Nat := 33660881985089762936023

theorem tailTrace_196663 : CollatzResearch.WordTrace tailWord_196663 prefixEnd_196663 33660881985089762936023 := by
  unfold tailWord_196663
  simp only [CollatzResearch.WordTrace]
  refine ⟨7172888886531013211482643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4781925924354008807655095 7172888886531013211482643)
  ·
    refine ⟨10759333329796519817223965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7172888886531013211482643 10759333329796519817223965)
    ·
      refine ⟨4034749998673694931458987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10759333329796519817223965 4034749998673694931458987)
      ·
        refine ⟨6052124998010542397188481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4034749998673694931458987 6052124998010542397188481)
        ·
          refine ⟨4539093748507906797891361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6052124998010542397188481 4539093748507906797891361)
          ·
            refine ⟨3404320311380930098418521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4539093748507906797891361 3404320311380930098418521)
            ·
              refine ⟨2553240233535697573813891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3404320311380930098418521 2553240233535697573813891)
              ·
                refine ⟨3829860350303546360720837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553240233535697573813891 3829860350303546360720837)
                ·
                  refine ⟨718098815681914942635157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3829860350303546360720837 718098815681914942635157)
                  ·
                    refine ⟨33660881985089762936023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 718098815681914942635157 33660881985089762936023)
                    ·
                      rfl

theorem cell23_196663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_196663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196663 prefixEnd_196663 := by exact prefixLift 196663
  have htrace : WordTrace (prefixWord ++ tailWord_196663) baseStart_196663 baseEnd_196663 := by
    simpa [prefixWord, tailWord_196663, baseEnd_196663] using wordTrace_append hprefix tailTrace_196663
  have hstable : (prefixWord ++ tailWord_196663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196663).length < 2 ^ (prefixWord ++ tailWord_196663).sum := by decide
  have hdescent : baseEnd_196663 < baseStart_196663 := by decide
  rcases family_descends (prefixWord ++ tailWord_196663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196703 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_196703 : Nat := 118140960795 + 196703 * 2 ^ 59
def prefixEnd_196703 : Nat := 4983230072969 + 3 ^ 40 * 196703 * 2
def baseEnd_196703 : Nat := 101003185181449132307885

theorem tailTrace_196703 : CollatzResearch.WordTrace tailWord_196703 prefixEnd_196703 101003185181449132307885 := by
  unfold tailWord_196703
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174347806386100042938763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4782898537590733361959175 7174347806386100042938763)
  ·
    refine ⟨10761521709579150064408145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7174347806386100042938763 10761521709579150064408145)
    ·
      refine ⟨8071141282184362548306109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10761521709579150064408145 8071141282184362548306109)
      ·
        refine ⟨3026677980819135955614791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8071141282184362548306109 3026677980819135955614791)
        ·
          refine ⟨4540016971228703933422187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026677980819135955614791 4540016971228703933422187)
          ·
            refine ⟨6810025456843055900133281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540016971228703933422187 6810025456843055900133281)
            ·
              refine ⟨5107519092632291925099961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6810025456843055900133281 5107519092632291925099961)
              ·
                refine ⟨3830639319474218943824971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5107519092632291925099961 3830639319474218943824971)
                ·
                  refine ⟨5745958979211328415737457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830639319474218943824971 5745958979211328415737457)
                  ·
                    refine ⟨4309469234408496311803093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5745958979211328415737457 4309469234408496311803093)
                    ·
                      refine ⟨101003185181449132307885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4309469234408496311803093 101003185181449132307885)
                      ·
                        rfl

theorem cell23_196703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_196703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196703 prefixEnd_196703 := by exact prefixLift 196703
  have htrace : WordTrace (prefixWord ++ tailWord_196703) baseStart_196703 baseEnd_196703 := by
    simpa [prefixWord, tailWord_196703, baseEnd_196703] using wordTrace_append hprefix tailTrace_196703
  have hstable : (prefixWord ++ tailWord_196703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196703).length < 2 ^ (prefixWord ++ tailWord_196703).sum := by decide
  have hdescent : baseEnd_196703 < baseStart_196703 := by decide
  rcases family_descends (prefixWord ++ tailWord_196703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196727 : List Nat := [1, 1, 3, 1, 1, 6, 1, 4, 5]
def baseStart_196727 : Nat := 118140960795 + 196727 * 2 ^ 59
def prefixEnd_196727 : Nat := 4983230072969 + 3 ^ 40 * 196727 * 2
def baseEnd_196727 : Nat := 11223945413017448711975

theorem tailTrace_196727 : CollatzResearch.WordTrace tailWord_196727 prefixEnd_196727 11223945413017448711975 := by
  unfold tailWord_196727
  simp only [CollatzResearch.WordTrace]
  refine ⟨7175223158299152141812435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4783482105532768094541623 7175223158299152141812435)
  ·
    refine ⟨10762834737448728212718653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7175223158299152141812435 10762834737448728212718653)
    ·
      refine ⟨4036063026543273079769495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10762834737448728212718653 4036063026543273079769495)
      ·
        refine ⟨6054094539814909619654243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4036063026543273079769495 6054094539814909619654243)
        ·
          refine ⟨9081141809722364429481365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6054094539814909619654243 9081141809722364429481365)
          ·
            refine ⟨425678522330735832631939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9081141809722364429481365 425678522330735832631939)
            ·
              refine ⟨638517783496103748947909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425678522330735832631939 638517783496103748947909)
              ·
                refine ⟨119722084405519452927733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 638517783496103748947909 119722084405519452927733)
                ·
                  refine ⟨11223945413017448711975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119722084405519452927733 11223945413017448711975)
                  ·
                    rfl

theorem cell23_196727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 5].length) (baseStart_196727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196727 prefixEnd_196727 := by exact prefixLift 196727
  have htrace : WordTrace (prefixWord ++ tailWord_196727) baseStart_196727 baseEnd_196727 := by
    simpa [prefixWord, tailWord_196727, baseEnd_196727] using wordTrace_append hprefix tailTrace_196727
  have hstable : (prefixWord ++ tailWord_196727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196727).length < 2 ^ (prefixWord ++ tailWord_196727).sum := by decide
  have hdescent : baseEnd_196727 < baseStart_196727 := by decide
  rcases family_descends (prefixWord ++ tailWord_196727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196740 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_196740 : Nat := 118140960795 + 196740 * 2 ^ 59
def prefixEnd_196740 : Nat := 4983230072969 + 3 ^ 40 * 196740 * 2
def baseEnd_196740 : Nat := 33674061321888495848405

theorem tailTrace_196740 : CollatzResearch.WordTrace tailWord_196740 prefixEnd_196740 33674061321888495848405 := by
  unfold tailWord_196740
  simp only [CollatzResearch.WordTrace]
  refine ⟨3587848653626027681017837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4783798204834703574690449 3587848653626027681017837)
  ·
    refine ⟨1345443245109760380381689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3587848653626027681017837 1345443245109760380381689)
    ·
      refine ⟨1009082433832320285286267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1345443245109760380381689 1009082433832320285286267)
      ·
        refine ⟨1513623650748480427929401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009082433832320285286267 1513623650748480427929401)
        ·
          refine ⟨1135217738061360320947051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1513623650748480427929401 1135217738061360320947051)
          ·
            refine ⟨1702826607092040481420577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135217738061360320947051 1702826607092040481420577)
            ·
              refine ⟨1277119955319030361065433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702826607092040481420577 1277119955319030361065433)
              ·
                refine ⟨957839966489272770799075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277119955319030361065433 957839966489272770799075)
                ·
                  refine ⟨1436759949733909156198613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957839966489272770799075 1436759949733909156198613)
                  ·
                    refine ⟨33674061321888495848405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1436759949733909156198613 33674061321888495848405)
                    ·
                      rfl

theorem cell23_196740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_196740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196740 prefixEnd_196740 := by exact prefixLift 196740
  have htrace : WordTrace (prefixWord ++ tailWord_196740) baseStart_196740 baseEnd_196740 := by
    simpa [prefixWord, tailWord_196740, baseEnd_196740] using wordTrace_append hprefix tailTrace_196740
  have hstable : (prefixWord ++ tailWord_196740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196740).length < 2 ^ (prefixWord ++ tailWord_196740).sum := by decide
  have hdescent : baseEnd_196740 < baseStart_196740 := by decide
  rcases family_descends (prefixWord ++ tailWord_196740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196804 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_196804 : Nat := 118140960795 + 196804 * 2 ^ 59
def prefixEnd_196804 : Nat := 4983230072969 + 3 ^ 40 * 196804 * 2
def baseEnd_196804 : Nat := 33685015575851079048307

theorem tailTrace_196804 : CollatzResearch.WordTrace tailWord_196804 prefixEnd_196804 33685015575851079048307 := by
  unfold tailWord_196804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3589015789510097146182733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4785354386013462861576977 3589015789510097146182733)
  ·
    refine ⟨1345880921066286429818525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3589015789510097146182733 1345880921066286429818525)
    ·
      refine ⟨504705345399857411181947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1345880921066286429818525 504705345399857411181947)
      ·
        refine ⟨757058018099786116772921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504705345399857411181947 757058018099786116772921)
        ·
          refine ⟨567793513574839587579691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757058018099786116772921 567793513574839587579691)
          ·
            refine ⟨851690270362259381369537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567793513574839587579691 851690270362259381369537)
            ·
              refine ⟨638767702771694536027153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851690270362259381369537 638767702771694536027153)
              ·
                refine ⟨479075777078770902020365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638767702771694536027153 479075777078770902020365)
                ·
                  refine ⟨179653416404539088257637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479075777078770902020365 179653416404539088257637)
                  ·
                    refine ⟨33685015575851079048307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179653416404539088257637 33685015575851079048307)
                    ·
                      rfl

theorem cell23_196804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_196804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196804 prefixEnd_196804 := by exact prefixLift 196804
  have htrace : WordTrace (prefixWord ++ tailWord_196804) baseStart_196804 baseEnd_196804 := by
    simpa [prefixWord, tailWord_196804, baseEnd_196804] using wordTrace_append hprefix tailTrace_196804
  have hstable : (prefixWord ++ tailWord_196804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196804).length < 2 ^ (prefixWord ++ tailWord_196804).sum := by decide
  have hdescent : baseEnd_196804 < baseStart_196804 := by decide
  rcases family_descends (prefixWord ++ tailWord_196804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196827 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 3]
def baseStart_196827 : Nat := 118140960795 + 196827 * 2 ^ 59
def prefixEnd_196827 : Nat := 4983230072969 + 3 ^ 40 * 196827 * 2
def baseEnd_196827 : Nat := 101066856782606647157315

theorem tailTrace_196827 : CollatzResearch.WordTrace tailWord_196827 prefixEnd_196827 101066856782606647157315 := by
  unfold tailWord_196827
  simp only [CollatzResearch.WordTrace]
  refine ⟨7178870457936869220452735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4785913638624579480301823 7178870457936869220452735)
  ·
    refine ⟨10768305686905303830679103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7178870457936869220452735 10768305686905303830679103)
    ·
      refine ⟨16152458530357955746018655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10768305686905303830679103 16152458530357955746018655)
      ·
        refine ⟨24228687795536933619027983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16152458530357955746018655 24228687795536933619027983)
        ·
          refine ⟨36343031693305400428541975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24228687795536933619027983 36343031693305400428541975)
          ·
            refine ⟨54514547539958100642812963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36343031693305400428541975 54514547539958100642812963)
            ·
              refine ⟨81771821309937150964219445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54514547539958100642812963 81771821309937150964219445)
              ·
                refine ⟨7666108247806607902895573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81771821309937150964219445 7666108247806607902895573)
                ·
                  refine ⟨179674412057967372724115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7666108247806607902895573 179674412057967372724115)
                  ·
                    refine ⟨269511618086951059086173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179674412057967372724115 269511618086951059086173)
                    ·
                      refine ⟨101066856782606647157315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 269511618086951059086173 101066856782606647157315)
                      ·
                        rfl

theorem cell23_196827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 3].length) (baseStart_196827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196827 prefixEnd_196827 := by exact prefixLift 196827
  have htrace : WordTrace (prefixWord ++ tailWord_196827) baseStart_196827 baseEnd_196827 := by
    simpa [prefixWord, tailWord_196827, baseEnd_196827] using wordTrace_append hprefix tailTrace_196827
  have hstable : (prefixWord ++ tailWord_196827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196827).length < 2 ^ (prefixWord ++ tailWord_196827).sum := by decide
  have hdescent : baseEnd_196827 < baseStart_196827 := by decide
  rcases family_descends (prefixWord ++ tailWord_196827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196854 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_196854 : Nat := 118140960795 + 196854 * 2 ^ 59
def prefixEnd_196854 : Nat := 4983230072969 + 3 ^ 40 * 196854 * 2
def baseEnd_196854 : Nat := 101080720760278041519691

theorem tailTrace_196854 : CollatzResearch.WordTrace tailWord_196854 prefixEnd_196854 101080720760278041519691 := by
  unfold tailWord_196854
  simp only [CollatzResearch.WordTrace]
  refine ⟨448740951802440801980351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4786570152559368554457077 448740951802440801980351)
  ·
    refine ⟨673111427703661202970527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 448740951802440801980351 673111427703661202970527)
    ·
      refine ⟨1009667141555491804455791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 673111427703661202970527 1009667141555491804455791)
      ·
        refine ⟨1514500712333237706683687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009667141555491804455791 1514500712333237706683687)
        ·
          refine ⟨2271751068499856560025531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514500712333237706683687 2271751068499856560025531)
          ·
            refine ⟨3407626602749784840038297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271751068499856560025531 3407626602749784840038297)
            ·
              refine ⟨2555719952062338630028723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407626602749784840038297 2555719952062338630028723)
              ·
                refine ⟨3833579928093507945043085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555719952062338630028723 3833579928093507945043085)
                ·
                  refine ⟨1437592473035065479391157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3833579928093507945043085 1437592473035065479391157)
                  ·
                    refine ⟨134774294347037388692921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1437592473035065479391157 134774294347037388692921)
                    ·
                      refine ⟨101080720760278041519691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134774294347037388692921 101080720760278041519691)
                      ·
                        rfl

theorem cell23_196854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_196854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196854 prefixEnd_196854 := by exact prefixLift 196854
  have htrace : WordTrace (prefixWord ++ tailWord_196854) baseStart_196854 baseEnd_196854 := by
    simpa [prefixWord, tailWord_196854, baseEnd_196854] using wordTrace_append hprefix tailTrace_196854
  have hstable : (prefixWord ++ tailWord_196854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196854).length < 2 ^ (prefixWord ++ tailWord_196854).sum := by decide
  have hdescent : baseEnd_196854 < baseStart_196854 := by decide
  rcases family_descends (prefixWord ++ tailWord_196854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196867 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 4]
def baseStart_196867 : Nat := 118140960795 + 196867 * 2 ^ 59
def prefixEnd_196867 : Nat := 4983230072969 + 3 ^ 40 * 196867 * 2
def baseEnd_196867 : Nat := 101087396008786490657131

theorem tailTrace_196867 : CollatzResearch.WordTrace tailWord_196867 prefixEnd_196867 101087396008786490657131 := by
  unfold tailWord_196867
  simp only [CollatzResearch.WordTrace]
  refine ⟨7180329377791956051908855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4786886251861304034605903 7180329377791956051908855)
  ·
    refine ⟨10770494066687934077863283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7180329377791956051908855 10770494066687934077863283)
    ·
      refine ⟨16155741100031901116794925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10770494066687934077863283 16155741100031901116794925)
      ·
        refine ⟨6058402912511962918798097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16155741100031901116794925 6058402912511962918798097)
        ·
          refine ⟨4543802184383972189098573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6058402912511962918798097 4543802184383972189098573)
          ·
            refine ⟨1703925819143989570911965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4543802184383972189098573 1703925819143989570911965)
            ·
              refine ⟨638972182178996089091987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1703925819143989570911965 638972182178996089091987)
              ·
                refine ⟨958458273268494133637981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638972182178996089091987 958458273268494133637981)
                ·
                  refine ⟨359421852475685300114243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958458273268494133637981 359421852475685300114243)
                  ·
                    refine ⟨539132778713527950171365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359421852475685300114243 539132778713527950171365)
                    ·
                      refine ⟨101087396008786490657131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 539132778713527950171365 101087396008786490657131)
                      ·
                        rfl

theorem cell23_196867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_196867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196867 prefixEnd_196867 := by exact prefixLift 196867
  have htrace : WordTrace (prefixWord ++ tailWord_196867) baseStart_196867 baseEnd_196867 := by
    simpa [prefixWord, tailWord_196867, baseEnd_196867] using wordTrace_append hprefix tailTrace_196867
  have hstable : (prefixWord ++ tailWord_196867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196867).length < 2 ^ (prefixWord ++ tailWord_196867).sum := by decide
  have hdescent : baseEnd_196867 < baseStart_196867 := by decide
  rcases family_descends (prefixWord ++ tailWord_196867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196890 : List Nat := [3, 1, 1, 3, 15]
def baseStart_196890 : Nat := 118140960795 + 196890 * 2 ^ 59
def prefixEnd_196890 : Nat := 4983230072969 + 3 ^ 40 * 196890 * 2
def baseEnd_196890 : Nat := 138682038496351029725

theorem tailTrace_196890 : CollatzResearch.WordTrace tailWord_196890 prefixEnd_196890 138682038496351029725 := by
  unfold tailWord_196890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1795292064177157744999031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4787445504472420653330749 1795292064177157744999031)
  ·
    refine ⟨2692938096265736617498547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1795292064177157744999031 2692938096265736617498547)
    ·
      refine ⟨4039407144398604926247821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692938096265736617498547 4039407144398604926247821)
      ·
        refine ⟨1514777679149476847342933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4039407144398604926247821 1514777679149476847342933)
        ·
          refine ⟨138682038496351029725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 1514777679149476847342933 138682038496351029725)
          ·
            rfl

theorem cell23_196890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 15].length) (baseStart_196890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196890 prefixEnd_196890 := by exact prefixLift 196890
  have htrace : WordTrace (prefixWord ++ tailWord_196890) baseStart_196890 baseEnd_196890 := by
    simpa [prefixWord, tailWord_196890, baseEnd_196890] using wordTrace_append hprefix tailTrace_196890
  have hstable : (prefixWord ++ tailWord_196890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196890).length < 2 ^ (prefixWord ++ tailWord_196890).sum := by decide
  have hdescent : baseEnd_196890 < baseStart_196890 := by decide
  rcases family_descends (prefixWord ++ tailWord_196890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196895 : List Nat := [1, 1, 2, 4, 3, 3, 2, 2, 1, 1, 3]
def baseStart_196895 : Nat := 118140960795 + 196895 * 2 ^ 59
def prefixEnd_196895 : Nat := 4983230072969 + 3 ^ 40 * 196895 * 2
def baseEnd_196895 : Nat := 101101773467112381107003

theorem tailTrace_196895 : CollatzResearch.WordTrace tailWord_196895 prefixEnd_196895 101101773467112381107003 := by
  unfold tailWord_196895
  simp only [CollatzResearch.WordTrace]
  refine ⟨7181350621690516833928139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4787567081127011222618759 7181350621690516833928139)
  ·
    refine ⟨10772025932535775250892209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7181350621690516833928139 10772025932535775250892209)
    ·
      refine ⟨8079019449401831438169157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10772025932535775250892209 8079019449401831438169157)
      ·
        refine ⟨1514816146762843394656717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8079019449401831438169157 1514816146762843394656717)
        ·
          refine ⟨568056055036066272996269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1514816146762843394656717 568056055036066272996269)
          ·
            refine ⟨213021020638524852373601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 568056055036066272996269 213021020638524852373601)
            ·
              refine ⟨159765765478893639280201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213021020638524852373601 159765765478893639280201)
              ·
                refine ⟨119824324109170229460151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159765765478893639280201 119824324109170229460151)
                ·
                  refine ⟨179736486163755344190227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119824324109170229460151 179736486163755344190227)
                  ·
                    refine ⟨269604729245633016285341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179736486163755344190227 269604729245633016285341)
                    ·
                      refine ⟨101101773467112381107003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 269604729245633016285341 101101773467112381107003)
                      ·
                        rfl

theorem cell23_196895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_196895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196895 prefixEnd_196895 := by exact prefixLift 196895
  have htrace : WordTrace (prefixWord ++ tailWord_196895) baseStart_196895 baseEnd_196895 := by
    simpa [prefixWord, tailWord_196895, baseEnd_196895] using wordTrace_append hprefix tailTrace_196895
  have hstable : (prefixWord ++ tailWord_196895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196895).length < 2 ^ (prefixWord ++ tailWord_196895).sum := by decide
  have hdescent : baseEnd_196895 < baseStart_196895 := by decide
  rcases family_descends (prefixWord ++ tailWord_196895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196977 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_196977 : Nat := 118140960795 + 196977 * 2 ^ 59
def prefixEnd_196977 : Nat := 4983230072969 + 3 ^ 40 * 196977 * 2
def baseEnd_196977 : Nat := 101143878880781060281625

theorem tailTrace_196977 : CollatzResearch.WordTrace tailWord_196977 prefixEnd_196977 101143878880781060281625 := by
  unfold tailWord_196977
  simp only [CollatzResearch.WordTrace]
  refine ⟨7184341407393444838413185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4789560938262296558942123 7184341407393444838413185)
  ·
    refine ⟨5388256055545083628809889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7184341407393444838413185 5388256055545083628809889)
    ·
      refine ⟨4041192041658812721607417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5388256055545083628809889 4041192041658812721607417)
      ·
        refine ⟨3030894031244109541205563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4041192041658812721607417 3030894031244109541205563)
        ·
          refine ⟨4546341046866164311808345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030894031244109541205563 4546341046866164311808345)
          ·
            refine ⟨3409755785149623233856259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4546341046866164311808345 3409755785149623233856259)
            ·
              refine ⟨5114633677724434850784389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409755785149623233856259 5114633677724434850784389)
              ·
                refine ⟨958993814573331534522073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5114633677724434850784389 958993814573331534522073)
                ·
                  refine ⟨719245360929998650891555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 958993814573331534522073 719245360929998650891555)
                  ·
                    refine ⟨1078868041394997976337333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 719245360929998650891555 1078868041394997976337333)
                    ·
                      refine ⟨101143878880781060281625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1078868041394997976337333 101143878880781060281625)
                      ·
                        rfl

theorem cell23_196977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_196977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196977 prefixEnd_196977 := by exact prefixLift 196977
  have htrace : WordTrace (prefixWord ++ tailWord_196977) baseStart_196977 baseEnd_196977 := by
    simpa [prefixWord, tailWord_196977, baseEnd_196977] using wordTrace_append hprefix tailTrace_196977
  have hstable : (prefixWord ++ tailWord_196977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196977).length < 2 ^ (prefixWord ++ tailWord_196977).sum := by decide
  have hdescent : baseEnd_196977 < baseStart_196977 := by decide
  rcases family_descends (prefixWord ++ tailWord_196977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196978 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_196978 : Nat := 118140960795 + 196978 * 2 ^ 59
def prefixEnd_196978 : Nat := 4983230072969 + 3 ^ 40 * 196978 * 2
def baseEnd_196978 : Nat := 101144392361435556369121

theorem tailTrace_196978 : CollatzResearch.WordTrace tailWord_196978 prefixEnd_196978 101144392361435556369121 := by
  unfold tailWord_196978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796094470097455502299897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4789585253593214672799725 1796094470097455502299897)
  ·
    refine ⟨1347070852573091626724923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1796094470097455502299897 1347070852573091626724923)
    ·
      refine ⟨2020606278859637440087385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1347070852573091626724923 2020606278859637440087385)
      ·
        refine ⟨1515454709144728080065539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2020606278859637440087385 1515454709144728080065539)
        ·
          refine ⟨2273182063717092120098309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515454709144728080065539 2273182063717092120098309)
          ·
            refine ⟨426221636946954772518433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2273182063717092120098309 426221636946954772518433)
            ·
              refine ⟨319666227710216079388825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426221636946954772518433 319666227710216079388825)
              ·
                refine ⟨239749670782662059541619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319666227710216079388825 239749670782662059541619)
                ·
                  refine ⟨359624506173993089312429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239749670782662059541619 359624506173993089312429)
                  ·
                    refine ⟨134859189815247408492161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 359624506173993089312429 134859189815247408492161)
                    ·
                      refine ⟨101144392361435556369121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134859189815247408492161 101144392361435556369121)
                      ·
                        rfl

theorem cell23_196978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_196978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_196978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_196978 prefixEnd_196978 := by exact prefixLift 196978
  have htrace : WordTrace (prefixWord ++ tailWord_196978) baseStart_196978 baseEnd_196978 := by
    simpa [prefixWord, tailWord_196978, baseEnd_196978] using wordTrace_append hprefix tailTrace_196978
  have hstable : (prefixWord ++ tailWord_196978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196978).length < 2 ^ (prefixWord ++ tailWord_196978).sum := by decide
  have hdescent : baseEnd_196978 < baseStart_196978 := by decide
  rcases family_descends (prefixWord ++ tailWord_196978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197054 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_197054 : Nat := 118140960795 + 197054 * 2 ^ 59
def prefixEnd_197054 : Nat := 4983230072969 + 3 ^ 40 * 197054 * 2
def baseEnd_197054 : Nat := 101183416891177259018771

theorem tailTrace_197054 : CollatzResearch.WordTrace tailWord_197054 prefixEnd_197054 101183416891177259018771 := by
  unfold tailWord_197054
  simp only [CollatzResearch.WordTrace]
  refine ⟨898393728514310873620777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4791433218742991325977477 898393728514310873620777)
  ·
    refine ⟨673795296385733155215583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 898393728514310873620777 673795296385733155215583)
    ·
      refine ⟨1010692944578599732823375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 673795296385733155215583 1010692944578599732823375)
      ·
        refine ⟨1516039416867899599235063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010692944578599732823375 1516039416867899599235063)
        ·
          refine ⟨2274059125301849398852595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516039416867899599235063 2274059125301849398852595)
          ·
            refine ⟨3411088687952774098278893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274059125301849398852595 3411088687952774098278893)
            ·
              refine ⟨1279158257982290286854585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3411088687952774098278893 1279158257982290286854585)
              ·
                refine ⟨959368693486717715140939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279158257982290286854585 959368693486717715140939)
                ·
                  refine ⟨1439053040230076572711409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959368693486717715140939 1439053040230076572711409)
                  ·
                    refine ⟨1079289780172557429533557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1439053040230076572711409 1079289780172557429533557)
                    ·
                      refine ⟨101183416891177259018771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1079289780172557429533557 101183416891177259018771)
                      ·
                        rfl

theorem cell23_197054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_197054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197054 prefixEnd_197054 := by exact prefixLift 197054
  have htrace : WordTrace (prefixWord ++ tailWord_197054) baseStart_197054 baseEnd_197054 := by
    simpa [prefixWord, tailWord_197054, baseEnd_197054] using wordTrace_append hprefix tailTrace_197054
  have hstable : (prefixWord ++ tailWord_197054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197054).length < 2 ^ (prefixWord ++ tailWord_197054).sum := by decide
  have hdescent : baseEnd_197054 < baseStart_197054 := by decide
  rcases family_descends (prefixWord ++ tailWord_197054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197067 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 5]
def baseStart_197067 : Nat := 118140960795 + 197067 * 2 ^ 59
def prefixEnd_197067 : Nat := 4983230072969 + 3 ^ 40 * 197067 * 2
def baseEnd_197067 : Nat := 101190092139685708156211

theorem tailTrace_197067 : CollatzResearch.WordTrace tailWord_197067 prefixEnd_197067 101190092139685708156211 := by
  unfold tailWord_197067
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187623977067390209189455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4791749318044926806126303 7187623977067390209189455)
  ·
    refine ⟨10781435965601085313784183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7187623977067390209189455 10781435965601085313784183)
    ·
      refine ⟨16172153948401627970676275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10781435965601085313784183 16172153948401627970676275)
      ·
        refine ⟨24258230922602441956014413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16172153948401627970676275 24258230922602441956014413)
        ·
          refine ⟨9096836595975915733505405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24258230922602441956014413 9096836595975915733505405)
          ·
            refine ⟨3411313723490968400064527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9096836595975915733505405 3411313723490968400064527)
            ·
              refine ⟨5116970585236452600096791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411313723490968400064527 5116970585236452600096791)
              ·
                refine ⟨7675455877854678900145187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116970585236452600096791 7675455877854678900145187)
                ·
                  refine ⟨11513183816782018350217781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675455877854678900145187 11513183816782018350217781)
                  ·
                    refine ⟨1079360982823314220332917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11513183816782018350217781 1079360982823314220332917)
                    ·
                      refine ⟨101190092139685708156211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1079360982823314220332917 101190092139685708156211)
                      ·
                        rfl

theorem cell23_197067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_197067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197067 prefixEnd_197067 := by exact prefixLift 197067
  have htrace : WordTrace (prefixWord ++ tailWord_197067) baseStart_197067 baseEnd_197067 := by
    simpa [prefixWord, tailWord_197067, baseEnd_197067] using wordTrace_append hprefix tailTrace_197067
  have hstable : (prefixWord ++ tailWord_197067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197067).length < 2 ^ (prefixWord ++ tailWord_197067).sum := by decide
  have hdescent : baseEnd_197067 < baseStart_197067 := by decide
  rcases family_descends (prefixWord ++ tailWord_197067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197081 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 2, 4, 2]
def baseStart_197081 : Nat := 118140960795 + 197081 * 2 ^ 59
def prefixEnd_197081 : Nat := 4983230072969 + 3 ^ 40 * 197081 * 2
def baseEnd_197081 : Nat := 101197280868848653381147

theorem tailTrace_197081 : CollatzResearch.WordTrace tailWord_197081 prefixEnd_197081 101197280868848653381147 := by
  unfold tailWord_197081
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188134599016670600199097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4792089732677780400132731 7188134599016670600199097)
  ·
    refine ⟨5391100949262502950149323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7188134599016670600199097 5391100949262502950149323)
    ·
      refine ⟨8086651423893754425223985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5391100949262502950149323 8086651423893754425223985)
      ·
        refine ⟨6064988567920315818917989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8086651423893754425223985 6064988567920315818917989)
        ·
          refine ⟨1137185356485059216047123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6064988567920315818917989 1137185356485059216047123)
          ·
            refine ⟨1705778034727588824070685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137185356485059216047123 1705778034727588824070685)
            ·
              refine ⟨639666763022845809026507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1705778034727588824070685 639666763022845809026507)
              ·
                refine ⟨959500144534268713539761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639666763022845809026507 959500144534268713539761)
                ·
                  refine ⟨719625108400701535154821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 959500144534268713539761 719625108400701535154821)
                  ·
                    refine ⟨134929707825131537841529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 719625108400701535154821 134929707825131537841529)
                    ·
                      refine ⟨101197280868848653381147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134929707825131537841529 101197280868848653381147)
                      ·
                        rfl

theorem cell23_197081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_197081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197081 prefixEnd_197081 := by exact prefixLift 197081
  have htrace : WordTrace (prefixWord ++ tailWord_197081) baseStart_197081 baseEnd_197081 := by
    simpa [prefixWord, tailWord_197081, baseEnd_197081] using wordTrace_append hprefix tailTrace_197081
  have hstable : (prefixWord ++ tailWord_197081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197081).length < 2 ^ (prefixWord ++ tailWord_197081).sum := by decide
  have hdescent : baseEnd_197081 < baseStart_197081 := by decide
  rcases family_descends (prefixWord ++ tailWord_197081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197098 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_197098 : Nat := 118140960795 + 197098 * 2 ^ 59
def prefixEnd_197098 : Nat := 4983230072969 + 3 ^ 40 * 197098 * 2
def baseEnd_197098 : Nat := 101206010039975086868569

theorem tailTrace_197098 : CollatzResearch.WordTrace tailWord_197098 prefixEnd_197098 101206010039975086868569 := by
  unfold tailWord_197098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797188659988770625891987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4792503093303388335711965 1797188659988770625891987)
  ·
    refine ⟨2695782989983155938837981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1797188659988770625891987 2695782989983155938837981)
    ·
      refine ⟨1010918621243683477064243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2695782989983155938837981 1010918621243683477064243)
      ·
        refine ⟨1516377931865525215596365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010918621243683477064243 1516377931865525215596365)
        ·
          refine ⟨568641724449571955848637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1516377931865525215596365 568641724449571955848637)
          ·
            refine ⟨213240646668589483443239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 568641724449571955848637 213240646668589483443239)
            ·
              refine ⟨319860970002884225164859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213240646668589483443239 319860970002884225164859)
              ·
                refine ⟨479791455004326337747289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319860970002884225164859 479791455004326337747289)
                ·
                  refine ⟨359843591253244753310467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479791455004326337747289 359843591253244753310467)
                  ·
                    refine ⟨539765386879867129965701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359843591253244753310467 539765386879867129965701)
                    ·
                      refine ⟨101206010039975086868569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 539765386879867129965701 101206010039975086868569)
                      ·
                        rfl

theorem cell23_197098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_197098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197098 prefixEnd_197098 := by exact prefixLift 197098
  have htrace : WordTrace (prefixWord ++ tailWord_197098) baseStart_197098 baseEnd_197098 := by
    simpa [prefixWord, tailWord_197098, baseEnd_197098] using wordTrace_append hprefix tailTrace_197098
  have hstable : (prefixWord ++ tailWord_197098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197098).length < 2 ^ (prefixWord ++ tailWord_197098).sum := by decide
  have hdescent : baseEnd_197098 < baseStart_197098 := by decide
  rcases family_descends (prefixWord ++ tailWord_197098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197121 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 6]
def baseStart_197121 : Nat := 118140960795 + 197121 * 2 ^ 59
def prefixEnd_197121 : Nat := 4983230072969 + 3 ^ 40 * 197121 * 2
def baseEnd_197121 : Nat := 11246424455003166320107

theorem tailTrace_197121 : CollatzResearch.WordTrace tailWord_197121 prefixEnd_197121 11246424455003166320107 := by
  unfold tailWord_197121
  simp only [CollatzResearch.WordTrace]
  refine ⟨7189593518871757431655217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4793062345914504954436811 7189593518871757431655217)
  ·
    refine ⟨5392195139153818073741413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7189593518871757431655217 5392195139153818073741413)
    ·
      refine ⟨1011036588591340888826515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5392195139153818073741413 1011036588591340888826515)
      ·
        refine ⟨1516554882887011333239773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011036588591340888826515 1516554882887011333239773)
        ·
          refine ⟨568708081082629249964915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1516554882887011333239773 568708081082629249964915)
          ·
            refine ⟨853062121623943874947373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568708081082629249964915 853062121623943874947373)
            ·
              refine ⟨319898295608978953105265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853062121623943874947373 319898295608978953105265)
              ·
                refine ⟨239923721706734214828949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319898295608978953105265 239923721706734214828949)
                ·
                  refine ⟨11246424455003166320107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239923721706734214828949 11246424455003166320107)
                  ·
                    rfl

theorem cell23_197121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 6].length) (baseStart_197121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197121 prefixEnd_197121 := by exact prefixLift 197121
  have htrace : WordTrace (prefixWord ++ tailWord_197121) baseStart_197121 baseEnd_197121 := by
    simpa [prefixWord, tailWord_197121, baseEnd_197121] using wordTrace_append hprefix tailTrace_197121
  have hstable : (prefixWord ++ tailWord_197121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197121).length < 2 ^ (prefixWord ++ tailWord_197121).sum := by decide
  have hdescent : baseEnd_197121 < baseStart_197121 := by decide
  rcases family_descends (prefixWord ++ tailWord_197121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197141 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_197141 : Nat := 118140960795 + 197141 * 2 ^ 59
def prefixEnd_197141 : Nat := 4983230072969 + 3 ^ 40 * 197141 * 2
def baseEnd_197141 : Nat := 101228089708118418630871

theorem tailTrace_197141 : CollatzResearch.WordTrace tailWord_197141 prefixEnd_197141 101228089708118418630871 := by
  unfold tailWord_197141
  simp only [CollatzResearch.WordTrace]
  refine ⟨7190322978799300847383277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4793548652532867231588851 7190322978799300847383277)
  ·
    refine ⟨2696371117049737817768729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7190322978799300847383277 2696371117049737817768729)
    ·
      refine ⟨2022278337787303363326547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2696371117049737817768729 2022278337787303363326547)
      ·
        refine ⟨3033417506680955044989821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022278337787303363326547 3033417506680955044989821)
        ·
          refine ⟨1137531565005358141871183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3033417506680955044989821 1137531565005358141871183)
          ·
            refine ⟨1706297347508037212806775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137531565005358141871183 1706297347508037212806775)
            ·
              refine ⟨2559446021262055819210163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706297347508037212806775 2559446021262055819210163)
              ·
                refine ⟨3839169031893083728815245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559446021262055819210163 3839169031893083728815245)
                ·
                  refine ⟨1439688386959906398305717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3839169031893083728815245 1439688386959906398305717)
                  ·
                    refine ⟨134970786277491224841161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1439688386959906398305717 134970786277491224841161)
                    ·
                      refine ⟨101228089708118418630871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 134970786277491224841161 101228089708118418630871)
                      ·
                        rfl

theorem cell23_197141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_197141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197141 prefixEnd_197141 := by exact prefixLift 197141
  have htrace : WordTrace (prefixWord ++ tailWord_197141) baseStart_197141 baseEnd_197141 := by
    simpa [prefixWord, tailWord_197141, baseEnd_197141] using wordTrace_append hprefix tailTrace_197141
  have hstable : (prefixWord ++ tailWord_197141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197141).length < 2 ^ (prefixWord ++ tailWord_197141).sum := by decide
  have hdescent : baseEnd_197141 < baseStart_197141 := by decide
  rcases family_descends (prefixWord ++ tailWord_197141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197148 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_197148 : Nat := 118140960795 + 197148 * 2 ^ 59
def prefixEnd_197148 : Nat := 4983230072969 + 3 ^ 40 * 197148 * 2
def baseEnd_197148 : Nat := 101231684072699891243339

theorem tailTrace_197148 : CollatzResearch.WordTrace tailWord_197148 prefixEnd_197148 101231684072699891243339 := by
  unfold tailWord_197148
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595289144886970521444049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4793718859849294028592065 3595289144886970521444049)
  ·
    refine ⟨2696466858665227891083037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3595289144886970521444049 2696466858665227891083037)
    ·
      refine ⟨1011175071999460459156139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2696466858665227891083037 1011175071999460459156139)
      ·
        refine ⟨1516762607999190688734209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011175071999460459156139 1516762607999190688734209)
        ·
          refine ⟨1137571955999393016550657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1516762607999190688734209 1137571955999393016550657)
          ·
            refine ⟨853178966999544762412993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137571955999393016550657 853178966999544762412993)
            ·
              refine ⟨639884225249658571809745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853178966999544762412993 639884225249658571809745)
              ·
                refine ⟨479913168937243928857309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639884225249658571809745 479913168937243928857309)
                ·
                  refine ⟨179967438351466473321491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479913168937243928857309 179967438351466473321491)
                  ·
                    refine ⟨269951157527199709982237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179967438351466473321491 269951157527199709982237)
                    ·
                      refine ⟨101231684072699891243339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 269951157527199709982237 101231684072699891243339)
                      ·
                        rfl

theorem cell23_197148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_197148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197148 prefixEnd_197148 := by exact prefixLift 197148
  have htrace : WordTrace (prefixWord ++ tailWord_197148) baseStart_197148 baseEnd_197148 := by
    simpa [prefixWord, tailWord_197148, baseEnd_197148] using wordTrace_append hprefix tailTrace_197148
  have hstable : (prefixWord ++ tailWord_197148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197148).length < 2 ^ (prefixWord ++ tailWord_197148).sum := by decide
  have hdescent : baseEnd_197148 < baseStart_197148 := by decide
  rcases family_descends (prefixWord ++ tailWord_197148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197159 : List Nat := [1, 1, 7, 2, 1, 2, 1, 3, 1, 4]
def baseStart_197159 : Nat := 118140960795 + 197159 * 2 ^ 59
def prefixEnd_197159 : Nat := 4983230072969 + 3 ^ 40 * 197159 * 2
def baseEnd_197159 : Nat := 33745777453299782735263

theorem tailTrace_197159 : CollatzResearch.WordTrace tailWord_197159 prefixEnd_197159 33745777453299782735263 := by
  unfold tailWord_197159
  simp only [CollatzResearch.WordTrace]
  refine ⟨7190979492734089921538531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4793986328489393281025687 7190979492734089921538531)
  ·
    refine ⟨10786469239101134882307797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7190979492734089921538531 10786469239101134882307797)
    ·
      refine ⟨252807872791432848804089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10786469239101134882307797 252807872791432848804089)
      ·
        refine ⟨189605904593574636603067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252807872791432848804089 189605904593574636603067)
        ·
          refine ⟨284408856890361954904601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189605904593574636603067 284408856890361954904601)
          ·
            refine ⟨213306642667771466178451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284408856890361954904601 213306642667771466178451)
            ·
              refine ⟨319959964001657199267677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213306642667771466178451 319959964001657199267677)
              ·
                refine ⟨119984986500621449725379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319959964001657199267677 119984986500621449725379)
                ·
                  refine ⟨179977479750932174588069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119984986500621449725379 179977479750932174588069)
                  ·
                    refine ⟨33745777453299782735263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179977479750932174588069 33745777453299782735263)
                    ·
                      rfl

theorem cell23_197159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_197159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197159 prefixEnd_197159 := by exact prefixLift 197159
  have htrace : WordTrace (prefixWord ++ tailWord_197159) baseStart_197159 baseEnd_197159 := by
    simpa [prefixWord, tailWord_197159, baseEnd_197159] using wordTrace_append hprefix tailTrace_197159
  have hstable : (prefixWord ++ tailWord_197159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197159).length < 2 ^ (prefixWord ++ tailWord_197159).sum := by decide
  have hdescent : baseEnd_197159 < baseStart_197159 := by decide
  rcases family_descends (prefixWord ++ tailWord_197159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197164 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_197164 : Nat := 118140960795 + 197164 * 2 ^ 59
def prefixEnd_197164 : Nat := 4983230072969 + 3 ^ 40 * 197164 * 2
def baseEnd_197164 : Nat := 33746633254390609547755

theorem tailTrace_197164 : CollatzResearch.WordTrace tailWord_197164 prefixEnd_197164 33746633254390609547755 := by
  unfold tailWord_197164
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595580928857987887735273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4794107905143983850313697 3595580928857987887735273)
  ·
    refine ⟨2696685696643490915801455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3595580928857987887735273 2696685696643490915801455)
    ·
      refine ⟨4045028544965236373702183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2696685696643490915801455 4045028544965236373702183)
      ·
        refine ⟨6067542817447854560553275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4045028544965236373702183 6067542817447854560553275)
        ·
          refine ⟨9101314226171781840829913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6067542817447854560553275 9101314226171781840829913)
          ·
            refine ⟨6825985669628836380622435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9101314226171781840829913 6825985669628836380622435)
            ·
              refine ⟨10238978504443254570933653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825985669628836380622435 10238978504443254570933653)
              ·
                refine ⟨479952117395777558012515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10238978504443254570933653 479952117395777558012515)
                ·
                  refine ⟨719928176093666337018773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479952117395777558012515 719928176093666337018773)
                  ·
                    refine ⟨33746633254390609547755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 719928176093666337018773 33746633254390609547755)
                    ·
                      rfl

theorem cell23_197164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_197164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197164 prefixEnd_197164 := by exact prefixLift 197164
  have htrace : WordTrace (prefixWord ++ tailWord_197164) baseStart_197164 baseEnd_197164 := by
    simpa [prefixWord, tailWord_197164, baseEnd_197164] using wordTrace_append hprefix tailTrace_197164
  have hstable : (prefixWord ++ tailWord_197164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197164).length < 2 ^ (prefixWord ++ tailWord_197164).sum := by decide
  have hdescent : baseEnd_197164 < baseStart_197164 := by decide
  rcases family_descends (prefixWord ++ tailWord_197164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197171 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 4]
def baseStart_197171 : Nat := 118140960795 + 197171 * 2 ^ 59
def prefixEnd_197171 : Nat := 4983230072969 + 3 ^ 40 * 197171 * 2
def baseEnd_197171 : Nat := 101243494127753301255733

theorem tailTrace_197171 : CollatzResearch.WordTrace tailWord_197171 prefixEnd_197171 101243494127753301255733 := by
  unfold tailWord_197171
  simp only [CollatzResearch.WordTrace]
  refine ⟨7191417168690615970975367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4794278112460410647316911 7191417168690615970975367)
  ·
    refine ⟨10787125753035923956463051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7191417168690615970975367 10787125753035923956463051)
    ·
      refine ⟨16180688629553885934694577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10787125753035923956463051 16180688629553885934694577)
      ·
        refine ⟨12135516472165414451020933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16180688629553885934694577 12135516472165414451020933)
        ·
          refine ⟨2275409338531015209566425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12135516472165414451020933 2275409338531015209566425)
          ·
            refine ⟨1706557003898261407174819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2275409338531015209566425 1706557003898261407174819)
            ·
              refine ⟨2559835505847392110762229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706557003898261407174819 2559835505847392110762229)
              ·
                refine ⟨239984578673193010383959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2559835505847392110762229 239984578673193010383959)
                ·
                  refine ⟨359976868009789515575939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239984578673193010383959 359976868009789515575939)
                  ·
                    refine ⟨539965302014684273363909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359976868009789515575939 539965302014684273363909)
                    ·
                      refine ⟨101243494127753301255733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 539965302014684273363909 101243494127753301255733)
                      ·
                        rfl

theorem cell23_197171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 4].length) (baseStart_197171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197171 prefixEnd_197171 := by exact prefixLift 197171
  have htrace : WordTrace (prefixWord ++ tailWord_197171) baseStart_197171 baseEnd_197171 := by
    simpa [prefixWord, tailWord_197171, baseEnd_197171] using wordTrace_append hprefix tailTrace_197171
  have hstable : (prefixWord ++ tailWord_197171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197171).length < 2 ^ (prefixWord ++ tailWord_197171).sum := by decide
  have hdescent : baseEnd_197171 < baseStart_197171 := by decide
  rcases family_descends (prefixWord ++ tailWord_197171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197184 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_197184 : Nat := 118140960795 + 197184 * 2 ^ 59
def prefixEnd_197184 : Nat := 4983230072969 + 3 ^ 40 * 197184 * 2
def baseEnd_197184 : Nat := 101250169376261750393173

theorem tailTrace_197184 : CollatzResearch.WordTrace tailWord_197184 prefixEnd_197184 101250169376261750393173 := by
  unfold tailWord_197184
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595945658821759595599303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4794594211762346127465737 3595945658821759595599303)
  ·
    refine ⟨5393918488232639393398955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3595945658821759595599303 5393918488232639393398955)
    ·
      refine ⟨8090877732348959090098433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5393918488232639393398955 8090877732348959090098433)
      ·
        refine ⟨6068158299261719317573825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8090877732348959090098433 6068158299261719317573825)
        ·
          refine ⟨4551118724446289488180369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6068158299261719317573825 4551118724446289488180369)
          ·
            refine ⟨3413339043334717116135277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4551118724446289488180369 3413339043334717116135277)
            ·
              refine ⟨1280002141250518918550729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3413339043334717116135277 1280002141250518918550729)
              ·
                refine ⟨960001605937889188913047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280002141250518918550729 960001605937889188913047)
                ·
                  refine ⟨1440002408906833783369571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960001605937889188913047 1440002408906833783369571)
                  ·
                    refine ⟨2160003613360250675054357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1440002408906833783369571 2160003613360250675054357)
                    ·
                      refine ⟨101250169376261750393173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2160003613360250675054357 101250169376261750393173)
                      ·
                        rfl

theorem cell23_197184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_197184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197184 prefixEnd_197184 := by exact prefixLift 197184
  have htrace : WordTrace (prefixWord ++ tailWord_197184) baseStart_197184 baseEnd_197184 := by
    simpa [prefixWord, tailWord_197184, baseEnd_197184] using wordTrace_append hprefix tailTrace_197184
  have hstable : (prefixWord ++ tailWord_197184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197184).length < 2 ^ (prefixWord ++ tailWord_197184).sum := by decide
  have hdescent : baseEnd_197184 < baseStart_197184 := by decide
  rcases family_descends (prefixWord ++ tailWord_197184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197191 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_197191 : Nat := 118140960795 + 197191 * 2 ^ 59
def prefixEnd_197191 : Nat := 4983230072969 + 3 ^ 40 * 197191 * 2
def baseEnd_197191 : Nat := 101253763740843223005641

theorem tailTrace_197191 : CollatzResearch.WordTrace tailWord_197191 prefixEnd_197191 101253763740843223005641 := by
  unfold tailWord_197191
  simp only [CollatzResearch.WordTrace]
  refine ⟨7192146628618159386703427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4794764419078772924468951 7192146628618159386703427)
  ·
    refine ⟨10788219942927239080055141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7192146628618159386703427 10788219942927239080055141)
    ·
      refine ⟨2022791239298857327510339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10788219942927239080055141 2022791239298857327510339)
      ·
        refine ⟨3034186858948285991265509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022791239298857327510339 3034186858948285991265509)
        ·
          refine ⟨568910036052803623362283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3034186858948285991265509 568910036052803623362283)
          ·
            refine ⟨853365054079205435043425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568910036052803623362283 853365054079205435043425)
            ·
              refine ⟨640023790559404076282569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853365054079205435043425 640023790559404076282569)
              ·
                refine ⟨480017842919553057211927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640023790559404076282569 480017842919553057211927)
                ·
                  refine ⟨720026764379329585817891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480017842919553057211927 720026764379329585817891)
                  ·
                    refine ⟨1080040146568994378726837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 720026764379329585817891 1080040146568994378726837)
                    ·
                      refine ⟨101253763740843223005641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1080040146568994378726837 101253763740843223005641)
                      ·
                        rfl

theorem cell23_197191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_197191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197191 prefixEnd_197191 := by exact prefixLift 197191
  have htrace : WordTrace (prefixWord ++ tailWord_197191) baseStart_197191 baseEnd_197191 := by
    simpa [prefixWord, tailWord_197191, baseEnd_197191] using wordTrace_append hprefix tailTrace_197191
  have hstable : (prefixWord ++ tailWord_197191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197191).length < 2 ^ (prefixWord ++ tailWord_197191).sum := by decide
  have hdescent : baseEnd_197191 < baseStart_197191 := by decide
  rcases family_descends (prefixWord ++ tailWord_197191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197194 : List Nat := [3, 1, 2, 1, 1, 4, 1, 10]
def baseStart_197194 : Nat := 118140960795 + 197194 * 2 ^ 59
def prefixEnd_197194 : Nat := 4983230072969 + 3 ^ 40 * 197194 * 2
def baseEnd_197194 : Nat := 3750196451215063380301

theorem tailTrace_197194 : CollatzResearch.WordTrace tailWord_197194 prefixEnd_197194 3750196451215063380301 := by
  unfold tailWord_197194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798064011901822724765659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4794837365071527266041757 1798064011901822724765659)
  ·
    refine ⟨2697096017852734087148489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1798064011901822724765659 2697096017852734087148489)
    ·
      refine ⟨2022822013389550565361367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2697096017852734087148489 2022822013389550565361367)
      ·
        refine ⟨3034233020084325848042051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022822013389550565361367 3034233020084325848042051)
        ·
          refine ⟨4551349530126488772063077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034233020084325848042051 4551349530126488772063077)
          ·
            refine ⟨853378036898716644761827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4551349530126488772063077 853378036898716644761827)
            ·
              refine ⟨1280067055348074967142741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853378036898716644761827 1280067055348074967142741)
              ·
                refine ⟨3750196451215063380301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1280067055348074967142741 3750196451215063380301)
                ·
                  rfl

theorem cell23_197194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 10].length) (baseStart_197194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197194 prefixEnd_197194 := by exact prefixLift 197194
  have htrace : WordTrace (prefixWord ++ tailWord_197194) baseStart_197194 baseEnd_197194 := by
    simpa [prefixWord, tailWord_197194, baseEnd_197194] using wordTrace_append hprefix tailTrace_197194
  have hstable : (prefixWord ++ tailWord_197194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197194).length < 2 ^ (prefixWord ++ tailWord_197194).sum := by decide
  have hdescent : baseEnd_197194 < baseStart_197194 := by decide
  rcases family_descends (prefixWord ++ tailWord_197194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197208 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 1, 2, 3]
def baseStart_197208 : Nat := 118140960795 + 197208 * 2 ^ 59
def prefixEnd_197208 : Nat := 4983230072969 + 3 ^ 40 * 197208 * 2
def baseEnd_197208 : Nat := 101262492911969656493063

theorem tailTrace_197208 : CollatzResearch.WordTrace tailWord_197208 prefixEnd_197208 101262492911969656493063 := by
  unfold tailWord_197208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3596383334778285645036139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4795177779704380860048185 3596383334778285645036139)
  ·
    refine ⟨5394575002167428467554209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3596383334778285645036139 5394575002167428467554209)
    ·
      refine ⟨4045931251625571350665657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5394575002167428467554209 4045931251625571350665657)
      ·
        refine ⟨3034448438719178512999243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4045931251625571350665657 3034448438719178512999243)
        ·
          refine ⟨4551672658078767769498865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034448438719178512999243 4551672658078767769498865)
          ·
            refine ⟨3413754493559075827124149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4551672658078767769498865 3413754493559075827124149)
            ·
              refine ⟨320039483771163358792889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3413754493559075827124149 320039483771163358792889)
              ·
                refine ⟨240029612828372519094667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320039483771163358792889 240029612828372519094667)
                ·
                  refine ⟨360044419242558778642001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240029612828372519094667 360044419242558778642001)
                  ·
                    refine ⟨270033314431919083981501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 360044419242558778642001 270033314431919083981501)
                    ·
                      refine ⟨101262492911969656493063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 270033314431919083981501 101262492911969656493063)
                      ·
                        rfl

theorem cell23_197208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_197208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197208 prefixEnd_197208 := by exact prefixLift 197208
  have htrace : WordTrace (prefixWord ++ tailWord_197208) baseStart_197208 baseEnd_197208 := by
    simpa [prefixWord, tailWord_197208, baseEnd_197208] using wordTrace_append hprefix tailTrace_197208
  have hstable : (prefixWord ++ tailWord_197208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197208).length < 2 ^ (prefixWord ++ tailWord_197208).sum := by decide
  have hdescent : baseEnd_197208 < baseStart_197208 := by decide
  rcases family_descends (prefixWord ++ tailWord_197208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197248 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 3, 3, 2]
def baseStart_197248 : Nat := 118140960795 + 197248 * 2 ^ 59
def prefixEnd_197248 : Nat := 4983230072969 + 3 ^ 40 * 197248 * 2
def baseEnd_197248 : Nat := 101283032138149499992879

theorem tailTrace_197248 : CollatzResearch.WordTrace tailWord_197248 prefixEnd_197248 101283032138149499992879 := by
  unfold tailWord_197248
  simp only [CollatzResearch.WordTrace]
  refine ⟨3597112794705829060764199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4796150392941105414352265 3597112794705829060764199)
  ·
    refine ⟨5395669192058743591146299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3597112794705829060764199 5395669192058743591146299)
    ·
      refine ⟨8093503788088115386719449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5395669192058743591146299 8093503788088115386719449)
      ·
        refine ⟨6070127841066086540039587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8093503788088115386719449 6070127841066086540039587)
        ·
          refine ⟨9105191761599129810059381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070127841066086540039587 9105191761599129810059381)
          ·
            refine ⟨853611727649918419693067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9105191761599129810059381 853611727649918419693067)
            ·
              refine ⟨1280417591474877629539601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853611727649918419693067 1280417591474877629539601)
              ·
                refine ⟨960313193606158222154701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280417591474877629539601 960313193606158222154701)
                ·
                  refine ⟨360117447602309333308013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960313193606158222154701 360117447602309333308013)
                  ·
                    refine ⟨135044042850865999990505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360117447602309333308013 135044042850865999990505)
                    ·
                      refine ⟨101283032138149499992879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135044042850865999990505 101283032138149499992879)
                      ·
                        rfl

theorem cell23_197248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_197248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197248 prefixEnd_197248 := by exact prefixLift 197248
  have htrace : WordTrace (prefixWord ++ tailWord_197248) baseStart_197248 baseEnd_197248 := by
    simpa [prefixWord, tailWord_197248, baseEnd_197248] using wordTrace_append hprefix tailTrace_197248
  have hstable : (prefixWord ++ tailWord_197248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197248).length < 2 ^ (prefixWord ++ tailWord_197248).sum := by decide
  have hdescent : baseEnd_197248 < baseStart_197248 := by decide
  rcases family_descends (prefixWord ++ tailWord_197248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197295 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 4, 2, 2]
def baseStart_197295 : Nat := 118140960795 + 197295 * 2 ^ 59
def prefixEnd_197295 : Nat := 4983230072969 + 3 ^ 40 * 197295 * 2
def baseEnd_197295 : Nat := 101307165728910816105163

theorem tailTrace_197295 : CollatzResearch.WordTrace tailWord_197295 prefixEnd_197295 101307165728910816105163 := by
  unfold tailWord_197295
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195939820241385148489339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4797293213494256765659559 7195939820241385148489339)
  ·
    refine ⟨10793909730362077722734009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7195939820241385148489339 10793909730362077722734009)
    ·
      refine ⟨8095432297771558292050507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10793909730362077722734009 8095432297771558292050507)
      ·
        refine ⟨12143148446657337438075761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8095432297771558292050507 12143148446657337438075761)
        ·
          refine ⟨9107361334993003078556821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12143148446657337438075761 9107361334993003078556821)
          ·
            refine ⟨426907562577797019307351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9107361334993003078556821 426907562577797019307351)
            ·
              refine ⟨640361343866695528961027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426907562577797019307351 640361343866695528961027)
              ·
                refine ⟨960542015800043293441541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640361343866695528961027 960542015800043293441541)
                ·
                  refine ⟨180101627962508117520289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 960542015800043293441541 180101627962508117520289)
                  ·
                    refine ⟨135076220971881088140217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 180101627962508117520289 135076220971881088140217)
                    ·
                      refine ⟨101307165728910816105163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135076220971881088140217 101307165728910816105163)
                      ·
                        rfl

theorem cell23_197295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 2, 2].length) (baseStart_197295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197295 prefixEnd_197295 := by exact prefixLift 197295
  have htrace : WordTrace (prefixWord ++ tailWord_197295) baseStart_197295 baseEnd_197295 := by
    simpa [prefixWord, tailWord_197295, baseEnd_197295] using wordTrace_append hprefix tailTrace_197295
  have hstable : (prefixWord ++ tailWord_197295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197295).length < 2 ^ (prefixWord ++ tailWord_197295).sum := by decide
  have hdescent : baseEnd_197295 < baseStart_197295 := by decide
  rcases family_descends (prefixWord ++ tailWord_197295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197335 : List Nat := [1, 1, 3, 2, 1, 6, 1, 3, 5]
def baseStart_197335 : Nat := 118140960795 + 197335 * 2 ^ 59
def prefixEnd_197335 : Nat := 4983230072969 + 3 ^ 40 * 197335 * 2
def baseEnd_197335 : Nat := 11258633883898962178331

theorem tailTrace_197335 : CollatzResearch.WordTrace tailWord_197335 prefixEnd_197335 11258633883898962178331 := by
  unfold tailWord_197335
  simp only [CollatzResearch.WordTrace]
  refine ⟨7197398740096471979945459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4798265826730981319963639 7197398740096471979945459)
  ·
    refine ⟨10796098110144707969918189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7197398740096471979945459 10796098110144707969918189)
    ·
      refine ⟨4048536791304265488719321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10796098110144707969918189 4048536791304265488719321)
      ·
        refine ⟨3036402593478199116539491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4048536791304265488719321 3036402593478199116539491)
        ·
          refine ⟨4554603890217298674809237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036402593478199116539491 4554603890217298674809237)
          ·
            refine ⟨213497057353935875381683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4554603890217298674809237 213497057353935875381683)
            ·
              refine ⟨320245586030903813072525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213497057353935875381683 320245586030903813072525)
              ·
                refine ⟨120092094761588929902197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320245586030903813072525 120092094761588929902197)
                ·
                  refine ⟨11258633883898962178331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120092094761588929902197 11258633883898962178331)
                  ·
                    rfl

theorem cell23_197335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 5].length) (baseStart_197335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197335 prefixEnd_197335 := by exact prefixLift 197335
  have htrace : WordTrace (prefixWord ++ tailWord_197335) baseStart_197335 baseEnd_197335 := by
    simpa [prefixWord, tailWord_197335, baseEnd_197335] using wordTrace_append hprefix tailTrace_197335
  have hstable : (prefixWord ++ tailWord_197335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197335).length < 2 ^ (prefixWord ++ tailWord_197335).sum := by decide
  have hdescent : baseEnd_197335 < baseStart_197335 := by decide
  rcases family_descends (prefixWord ++ tailWord_197335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197348 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_197348 : Nat := 118140960795 + 197348 * 2 ^ 59
def prefixEnd_197348 : Nat := 4983230072969 + 3 ^ 40 * 197348 * 2
def baseEnd_197348 : Nat := 33778126734533036247473

theorem tailTrace_197348 : CollatzResearch.WordTrace tailWord_197348 prefixEnd_197348 33778126734533036247473 := by
  unfold tailWord_197348
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598936444524687600084349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4798581926032916800112465 3598936444524687600084349)
  ·
    refine ⟨1349601166696757850031631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3598936444524687600084349 1349601166696757850031631)
    ·
      refine ⟨2024401750045136775047447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1349601166696757850031631 2024401750045136775047447)
      ·
        refine ⟨3036602625067705162571171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024401750045136775047447 3036602625067705162571171)
        ·
          refine ⟨4554903937601557743856757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036602625067705162571171 4554903937601557743856757)
          ·
            refine ⟨427022244150146038486571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4554903937601557743856757 427022244150146038486571)
            ·
              refine ⟨640533366225219057729857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427022244150146038486571 640533366225219057729857)
              ·
                refine ⟨480400024668914293297393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640533366225219057729857 480400024668914293297393)
                ·
                  refine ⟨360300018501685719973045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480400024668914293297393 360300018501685719973045)
                  ·
                    refine ⟨33778126734533036247473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 360300018501685719973045 33778126734533036247473)
                    ·
                      rfl

theorem cell23_197348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_197348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197348 prefixEnd_197348 := by exact prefixLift 197348
  have htrace : WordTrace (prefixWord ++ tailWord_197348) baseStart_197348 baseEnd_197348 := by
    simpa [prefixWord, tailWord_197348, baseEnd_197348] using wordTrace_append hprefix tailTrace_197348
  have hstable : (prefixWord ++ tailWord_197348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197348).length < 2 ^ (prefixWord ++ tailWord_197348).sum := by decide
  have hdescent : baseEnd_197348 < baseStart_197348 := by decide
  rcases family_descends (prefixWord ++ tailWord_197348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197352 : List Nat := [2, 1, 4, 1, 4, 1, 3, 2, 5]
def baseStart_197352 : Nat := 118140960795 + 197352 * 2 ^ 59
def prefixEnd_197352 : Nat := 4983230072969 + 3 ^ 40 * 197352 * 2
def baseEnd_197352 : Nat := 11259603791801899232489

theorem tailTrace_197352 : CollatzResearch.WordTrace tailWord_197352 prefixEnd_197352 11259603791801899232489 := by
  unfold tailWord_197352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599009390517441941657155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4798679187356589255542873 3599009390517441941657155)
  ·
    refine ⟨5398514085776162912485733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3599009390517441941657155 5398514085776162912485733)
    ·
      refine ⟨1012221391083030546091075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5398514085776162912485733 1012221391083030546091075)
      ·
        refine ⟨1518332086624545819136613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012221391083030546091075 1518332086624545819136613)
        ·
          refine ⟨284687266242102341088115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1518332086624545819136613 284687266242102341088115)
          ·
            refine ⟨427030899363153511632173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284687266242102341088115 427030899363153511632173)
            ·
              refine ⟨160136587261182566862065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427030899363153511632173 160136587261182566862065)
              ·
                refine ⟨120102440445886925146549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160136587261182566862065 120102440445886925146549)
                ·
                  refine ⟨11259603791801899232489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120102440445886925146549 11259603791801899232489)
                  ·
                    rfl

theorem cell23_197352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 5].length) (baseStart_197352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197352 prefixEnd_197352 := by exact prefixLift 197352
  have htrace : WordTrace (prefixWord ++ tailWord_197352) baseStart_197352 baseEnd_197352 := by
    simpa [prefixWord, tailWord_197352, baseEnd_197352] using wordTrace_append hprefix tailTrace_197352
  have hstable : (prefixWord ++ tailWord_197352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197352).length < 2 ^ (prefixWord ++ tailWord_197352).sum := by decide
  have hdescent : baseEnd_197352 < baseStart_197352 := by decide
  rcases family_descends (prefixWord ++ tailWord_197352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197358 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_197358 : Nat := 118140960795 + 197358 * 2 ^ 59
def prefixEnd_197358 : Nat := 4983230072969 + 3 ^ 40 * 197358 * 2
def baseEnd_197358 : Nat := 101339515010144069617373

theorem tailTrace_197358 : CollatzResearch.WordTrace tailWord_197358 prefixEnd_197358 101339515010144069617373 := by
  unfold tailWord_197358
  simp only [CollatzResearch.WordTrace]
  refine ⟨899779702376643363504091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4798825079342097938688485 899779702376643363504091)
  ·
    refine ⟨1349669553564965045256137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 899779702376643363504091 1349669553564965045256137)
    ·
      refine ⟨1012252165173723783942103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1349669553564965045256137 1012252165173723783942103)
      ·
        refine ⟨1518378247760585675913155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012252165173723783942103 1518378247760585675913155)
        ·
          refine ⟨2277567371640878513869733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518378247760585675913155 2277567371640878513869733)
          ·
            refine ⟨427043882182664721350575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2277567371640878513869733 427043882182664721350575)
            ·
              refine ⟨640565823273997082025863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427043882182664721350575 640565823273997082025863)
              ·
                refine ⟨960848734910995623038795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640565823273997082025863 960848734910995623038795)
                ·
                  refine ⟨1441273102366493434558193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960848734910995623038795 1441273102366493434558193)
                  ·
                    refine ⟨1080954826774870075918645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1441273102366493434558193 1080954826774870075918645)
                    ·
                      refine ⟨101339515010144069617373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1080954826774870075918645 101339515010144069617373)
                      ·
                        rfl

theorem cell23_197358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_197358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197358 prefixEnd_197358 := by exact prefixLift 197358
  have htrace : WordTrace (prefixWord ++ tailWord_197358) baseStart_197358 baseEnd_197358 := by
    simpa [prefixWord, tailWord_197358, baseEnd_197358] using wordTrace_append hprefix tailTrace_197358
  have hstable : (prefixWord ++ tailWord_197358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197358).length < 2 ^ (prefixWord ++ tailWord_197358).sum := by decide
  have hdescent : baseEnd_197358 < baseStart_197358 := by decide
  rcases family_descends (prefixWord ++ tailWord_197358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197368 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 1, 6, 2]
def baseStart_197368 : Nat := 118140960795 + 197368 * 2 ^ 59
def prefixEnd_197368 : Nat := 4983230072969 + 3 ^ 40 * 197368 * 2
def baseEnd_197368 : Nat := 101344649816689030492327

theorem tailTrace_197368 : CollatzResearch.WordTrace tailWord_197368 prefixEnd_197368 101344649816689030492327 := by
  unfold tailWord_197368
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599301174488459307948379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4799068232651279077264505 3599301174488459307948379)
  ·
    refine ⟨5398951761732688961922569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3599301174488459307948379 5398951761732688961922569)
    ·
      refine ⟨4049213821299516721441927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5398951761732688961922569 4049213821299516721441927)
      ·
        refine ⟨6073820731949275082162891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049213821299516721441927 6073820731949275082162891)
        ·
          refine ⟨9110731097923912623244337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073820731949275082162891 9110731097923912623244337)
          ·
            refine ⟨6833048323442934467433253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9110731097923912623244337 6833048323442934467433253)
            ·
              refine ⟨1281196560645550212643735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6833048323442934467433253 1281196560645550212643735)
              ·
                refine ⟨1921794840968325318965603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281196560645550212643735 1921794840968325318965603)
                ·
                  refine ⟨2882692261452487978448405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921794840968325318965603 2882692261452487978448405)
                  ·
                    refine ⟨135126199755585373989769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2882692261452487978448405 135126199755585373989769)
                    ·
                      refine ⟨101344649816689030492327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135126199755585373989769 101344649816689030492327)
                      ·
                        rfl

theorem cell23_197368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_197368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197368 prefixEnd_197368 := by exact prefixLift 197368
  have htrace : WordTrace (prefixWord ++ tailWord_197368) baseStart_197368 baseEnd_197368 := by
    simpa [prefixWord, tailWord_197368, baseEnd_197368] using wordTrace_append hprefix tailTrace_197368
  have hstable : (prefixWord ++ tailWord_197368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197368).length < 2 ^ (prefixWord ++ tailWord_197368).sum := by decide
  have hdescent : baseEnd_197368 < baseStart_197368 := by decide
  rcases family_descends (prefixWord ++ tailWord_197368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197381 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_197381 : Nat := 118140960795 + 197381 * 2 ^ 59
def prefixEnd_197381 : Nat := 4983230072969 + 3 ^ 40 * 197381 * 2
def baseEnd_197381 : Nat := 101351325065197479629767

theorem tailTrace_197381 : CollatzResearch.WordTrace tailWord_197381 prefixEnd_197381 101351325065197479629767 := by
  unfold tailWord_197381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199076497929821836119997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4799384331953214557413331 7199076497929821836119997)
  ·
    refine ⟨2699653686723683188544999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7199076497929821836119997 2699653686723683188544999)
    ·
      refine ⟨4049480530085524782817499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2699653686723683188544999 4049480530085524782817499)
      ·
        refine ⟨6074220795128287174226249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049480530085524782817499 6074220795128287174226249)
        ·
          refine ⟨4555665596346215380669687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074220795128287174226249 4555665596346215380669687)
          ·
            refine ⟨6833498394519323071004531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555665596346215380669687 6833498394519323071004531)
            ·
              refine ⟨10250247591778984606506797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833498394519323071004531 10250247591778984606506797)
              ·
                refine ⟨3843842846917119227440049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10250247591778984606506797 3843842846917119227440049)
                ·
                  refine ⟨2882882135187839420580037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3843842846917119227440049 2882882135187839420580037)
                  ·
                    refine ⟨540540400347719891358757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2882882135187839420580037 540540400347719891358757)
                    ·
                      refine ⟨101351325065197479629767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 540540400347719891358757 101351325065197479629767)
                      ·
                        rfl

theorem cell23_197381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_197381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197381 prefixEnd_197381 := by exact prefixLift 197381
  have htrace : WordTrace (prefixWord ++ tailWord_197381) baseStart_197381 baseEnd_197381 := by
    simpa [prefixWord, tailWord_197381, baseEnd_197381] using wordTrace_append hprefix tailTrace_197381
  have hstable : (prefixWord ++ tailWord_197381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197381).length < 2 ^ (prefixWord ++ tailWord_197381).sum := by decide
  have hdescent : baseEnd_197381 < baseStart_197381 := by decide
  rcases family_descends (prefixWord ++ tailWord_197381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197395 : List Nat := [1, 1, 1, 2, 1, 3, 4, 5, 1, 4]
def baseStart_197395 : Nat := 118140960795 + 197395 * 2 ^ 59
def prefixEnd_197395 : Nat := 4983230072969 + 3 ^ 40 * 197395 * 2
def baseEnd_197395 : Nat := 33786171264786808284901

theorem tailTrace_197395 : CollatzResearch.WordTrace tailWord_197395 prefixEnd_197395 33786171264786808284901 := by
  unfold tailWord_197395
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199587119879102227129639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4799724746586068151419759 7199587119879102227129639)
  ·
    refine ⟨10799380679818653340694459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7199587119879102227129639 10799380679818653340694459)
    ·
      refine ⟨16199071019727980011041689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799380679818653340694459 16199071019727980011041689)
      ·
        refine ⟨12149303264795985008281267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16199071019727980011041689 12149303264795985008281267)
        ·
          refine ⟨18223954897193977512421901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12149303264795985008281267 18223954897193977512421901)
          ·
            refine ⟨6833983086447741567158213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18223954897193977512421901 6833983086447741567158213)
            ·
              refine ⟨1281371828708951543842165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6833983086447741567158213 1281371828708951543842165)
              ·
                refine ⟨120128608941464207235203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1281371828708951543842165 120128608941464207235203)
                ·
                  refine ⟨180192913412196310852805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120128608941464207235203 180192913412196310852805)
                  ·
                    refine ⟨33786171264786808284901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 180192913412196310852805 33786171264786808284901)
                    ·
                      rfl

theorem cell23_197395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 4].length) (baseStart_197395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197395 prefixEnd_197395 := by exact prefixLift 197395
  have htrace : WordTrace (prefixWord ++ tailWord_197395) baseStart_197395 baseEnd_197395 := by
    simpa [prefixWord, tailWord_197395, baseEnd_197395] using wordTrace_append hprefix tailTrace_197395
  have hstable : (prefixWord ++ tailWord_197395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197395).length < 2 ^ (prefixWord ++ tailWord_197395).sum := by decide
  have hdescent : baseEnd_197395 < baseStart_197395 := by decide
  rcases family_descends (prefixWord ++ tailWord_197395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197408 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 6]
def baseStart_197408 : Nat := 118140960795 + 197408 * 2 ^ 59
def prefixEnd_197408 : Nat := 4983230072969 + 3 ^ 40 * 197408 * 2
def baseEnd_197408 : Nat := 11262798782540985999127

theorem tailTrace_197408 : CollatzResearch.WordTrace tailWord_197408 prefixEnd_197408 11262798782540985999127 := by
  unfold tailWord_197408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600030634416002723676439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4800040845888003631568585 3600030634416002723676439)
  ·
    refine ⟨5400045951624004085514659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3600030634416002723676439 5400045951624004085514659)
    ·
      refine ⟨8100068927436006128271989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5400045951624004085514659 8100068927436006128271989)
      ·
        refine ⟨759381461947125574525499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8100068927436006128271989 759381461947125574525499)
        ·
          refine ⟨1139072192920688361788249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759381461947125574525499 1139072192920688361788249)
          ·
            refine ⟨854304144690516271341187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139072192920688361788249 854304144690516271341187)
            ·
              refine ⟨1281456217035774407011781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854304144690516271341187 1281456217035774407011781)
              ·
                refine ⟨240273040694207701314709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1281456217035774407011781 240273040694207701314709)
                ·
                  refine ⟨11262798782540985999127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240273040694207701314709 11262798782540985999127)
                  ·
                    rfl

theorem cell23_197408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 6].length) (baseStart_197408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197408 prefixEnd_197408 := by exact prefixLift 197408
  have htrace : WordTrace (prefixWord ++ tailWord_197408) baseStart_197408 baseEnd_197408 := by
    simpa [prefixWord, tailWord_197408, baseEnd_197408] using wordTrace_append hprefix tailTrace_197408
  have hstable : (prefixWord ++ tailWord_197408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197408).length < 2 ^ (prefixWord ++ tailWord_197408).sum := by decide
  have hdescent : baseEnd_197408 < baseStart_197408 := by decide
  rcases family_descends (prefixWord ++ tailWord_197408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197411 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 6]
def baseStart_197411 : Nat := 118140960795 + 197411 * 2 ^ 59
def prefixEnd_197411 : Nat := 4983230072969 + 3 ^ 40 * 197411 * 2
def baseEnd_197411 : Nat := 101366729484832362254629

theorem tailTrace_197411 : CollatzResearch.WordTrace tailWord_197411 prefixEnd_197411 101366729484832362254629 := by
  unfold tailWord_197411
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200170687821136959712087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4800113791880757973141391 7200170687821136959712087)
  ·
    refine ⟨10800256031731705439568131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7200170687821136959712087 10800256031731705439568131)
    ·
      refine ⟨16200384047597558159352197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10800256031731705439568131 16200384047597558159352197)
      ·
        refine ⟨3037572008924542154878537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16200384047597558159352197 3037572008924542154878537)
        ·
          refine ⟨2278179006693406616158903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3037572008924542154878537 2278179006693406616158903)
          ·
            refine ⟨3417268510040109924238355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278179006693406616158903 3417268510040109924238355)
            ·
              refine ⟨5125902765060164886357533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3417268510040109924238355 5125902765060164886357533)
              ·
                refine ⟨1922213536897561832384075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5125902765060164886357533 1922213536897561832384075)
                ·
                  refine ⟨2883320305346342748576113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922213536897561832384075 2883320305346342748576113)
                  ·
                    refine ⟨2162490229009757061432085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2883320305346342748576113 2162490229009757061432085)
                    ·
                      refine ⟨101366729484832362254629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2162490229009757061432085 101366729484832362254629)
                      ·
                        rfl

theorem cell23_197411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_197411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197411 prefixEnd_197411 := by exact prefixLift 197411
  have htrace : WordTrace (prefixWord ++ tailWord_197411) baseStart_197411 baseEnd_197411 := by
    simpa [prefixWord, tailWord_197411, baseEnd_197411] using wordTrace_append hprefix tailTrace_197411
  have hstable : (prefixWord ++ tailWord_197411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197411).length < 2 ^ (prefixWord ++ tailWord_197411).sum := by decide
  have hdescent : baseEnd_197411 < baseStart_197411 := by decide
  rcases family_descends (prefixWord ++ tailWord_197411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197431 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_197431 : Nat := 118140960795 + 197431 * 2 ^ 59
def prefixEnd_197431 : Nat := 4983230072969 + 3 ^ 40 * 197431 * 2
def baseEnd_197431 : Nat := 101376999097922284004537

theorem tailTrace_197431 : CollatzResearch.WordTrace tailWord_197431 prefixEnd_197431 101376999097922284004537 := by
  unfold tailWord_197431
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200900147748680375440147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4800600098499120250293431 7200900147748680375440147)
  ·
    refine ⟨10801350221623020563160221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7200900147748680375440147 10801350221623020563160221)
    ·
      refine ⟨4050506333108632711185083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10801350221623020563160221 4050506333108632711185083)
      ·
        refine ⟨6075759499662949066777625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050506333108632711185083 6075759499662949066777625)
        ·
          refine ⟨4556819624747211800083219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6075759499662949066777625 4556819624747211800083219)
          ·
            refine ⟨6835229437120817700124829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556819624747211800083219 6835229437120817700124829)
            ·
              refine ⟨2563211038920306637546811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6835229437120817700124829 2563211038920306637546811)
              ·
                refine ⟨3844816558380459956320217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563211038920306637546811 3844816558380459956320217)
                ·
                  refine ⟨2883612418785344967240163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3844816558380459956320217 2883612418785344967240163)
                  ·
                    refine ⟨4325418628178017450860245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2883612418785344967240163 4325418628178017450860245)
                    ·
                      refine ⟨101376999097922284004537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4325418628178017450860245 101376999097922284004537)
                      ·
                        rfl

theorem cell23_197431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_197431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197431 prefixEnd_197431 := by exact prefixLift 197431
  have htrace : WordTrace (prefixWord ++ tailWord_197431) baseStart_197431 baseEnd_197431 := by
    simpa [prefixWord, tailWord_197431, baseEnd_197431] using wordTrace_append hprefix tailTrace_197431
  have hstable : (prefixWord ++ tailWord_197431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197431).length < 2 ^ (prefixWord ++ tailWord_197431).sum := by decide
  have hdescent : baseEnd_197431 < baseStart_197431 := by decide
  rcases family_descends (prefixWord ++ tailWord_197431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197445 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 2, 3, 2]
def baseStart_197445 : Nat := 118140960795 + 197445 * 2 ^ 59
def prefixEnd_197445 : Nat := 4983230072969 + 3 ^ 40 * 197445 * 2
def baseEnd_197445 : Nat := 101384187827085229229473

theorem tailTrace_197445 : CollatzResearch.WordTrace tailWord_197445 prefixEnd_197445 101384187827085229229473 := by
  unfold tailWord_197445
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201410769697960766449789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4800940513131973844299859 7201410769697960766449789)
  ·
    refine ⟨2700529038636735287418671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7201410769697960766449789 2700529038636735287418671)
    ·
      refine ⟨4050793557955102931128007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700529038636735287418671 4050793557955102931128007)
      ·
        refine ⟨6076190336932654396692011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050793557955102931128007 6076190336932654396692011)
        ·
          refine ⟨9114285505398981595038017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076190336932654396692011 9114285505398981595038017)
          ·
            refine ⟨6835714129049236196278513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9114285505398981595038017 6835714129049236196278513)
            ·
              refine ⟨5126785596786927147208885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6835714129049236196278513 5126785596786927147208885)
              ·
                refine ⟨480636149698774420050833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5126785596786927147208885 480636149698774420050833)
                ·
                  refine ⟨360477112274080815038125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480636149698774420050833 360477112274080815038125)
                  ·
                    refine ⟨135178917102780305639297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360477112274080815038125 135178917102780305639297)
                    ·
                      refine ⟨101384187827085229229473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135178917102780305639297 101384187827085229229473)
                      ·
                        rfl

theorem cell23_197445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_197445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197445 prefixEnd_197445 := by exact prefixLift 197445
  have htrace : WordTrace (prefixWord ++ tailWord_197445) baseStart_197445 baseEnd_197445 := by
    simpa [prefixWord, tailWord_197445, baseEnd_197445] using wordTrace_append hprefix tailTrace_197445
  have hstable : (prefixWord ++ tailWord_197445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197445).length < 2 ^ (prefixWord ++ tailWord_197445).sum := by decide
  have hdescent : baseEnd_197445 < baseStart_197445 := by decide
  rcases family_descends (prefixWord ++ tailWord_197445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197512 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_197512 : Nat := 118140960795 + 197512 * 2 ^ 59
def prefixEnd_197512 : Nat := 4983230072969 + 3 ^ 40 * 197512 * 2
def baseEnd_197512 : Nat := 101418591030936467091665

theorem tailTrace_197512 : CollatzResearch.WordTrace tailWord_197512 prefixEnd_197512 101418591030936467091665 := by
  unfold tailWord_197512
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601927230227615604569395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4802569640303487472759193 3601927230227615604569395)
  ·
    refine ⟨5402890845341423406854093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3601927230227615604569395 5402890845341423406854093)
    ·
      refine ⟨2026084067003033777570285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5402890845341423406854093 2026084067003033777570285)
      ·
        refine ⟨759781525126137666588857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2026084067003033777570285 759781525126137666588857)
        ·
          refine ⟨569836143844603249941643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 759781525126137666588857 569836143844603249941643)
          ·
            refine ⟨854754215766904874912465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569836143844603249941643 854754215766904874912465)
            ·
              refine ⟨641065661825178656184349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854754215766904874912465 641065661825178656184349)
              ·
                refine ⟨240399623184441996069131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 641065661825178656184349 240399623184441996069131)
                ·
                  refine ⟨360599434776662994103697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240399623184441996069131 360599434776662994103697)
                  ·
                    refine ⟨270449576082497245577773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 360599434776662994103697 270449576082497245577773)
                    ·
                      refine ⟨101418591030936467091665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 270449576082497245577773 101418591030936467091665)
                      ·
                        rfl

theorem cell23_197512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_197512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197512 prefixEnd_197512 := by exact prefixLift 197512
  have htrace : WordTrace (prefixWord ++ tailWord_197512) baseStart_197512 baseEnd_197512 := by
    simpa [prefixWord, tailWord_197512, baseEnd_197512] using wordTrace_append hprefix tailTrace_197512
  have hstable : (prefixWord ++ tailWord_197512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197512).length < 2 ^ (prefixWord ++ tailWord_197512).sum := by decide
  have hdescent : baseEnd_197512 < baseStart_197512 := by decide
  rcases family_descends (prefixWord ++ tailWord_197512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197548 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_197548 : Nat := 118140960795 + 197548 * 2 ^ 59
def prefixEnd_197548 : Nat := 4983230072969 + 3 ^ 40 * 197548 * 2
def baseEnd_197548 : Nat := 101437076334498326241499

theorem tailTrace_197548 : CollatzResearch.WordTrace tailWord_197548 prefixEnd_197548 101437076334498326241499 := by
  unfold tailWord_197548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3602583744162404678724649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4803444992216539571632865 3602583744162404678724649)
  ·
    refine ⟨2701937808121803509043487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3602583744162404678724649 2701937808121803509043487)
    ·
      refine ⟨4052906712182705263565231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2701937808121803509043487 4052906712182705263565231)
      ·
        refine ⟨6079360068274057895347847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4052906712182705263565231 6079360068274057895347847)
        ·
          refine ⟨9119040102411086843021771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079360068274057895347847 9119040102411086843021771)
          ·
            refine ⟨13678560153616630264532657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119040102411086843021771 13678560153616630264532657)
            ·
              refine ⟨10258920115212472698399493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13678560153616630264532657 10258920115212472698399493)
              ·
                refine ⟨1923547521602338630949905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10258920115212472698399493 1923547521602338630949905)
                ·
                  refine ⟨1442660641201753973212429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1923547521602338630949905 1442660641201753973212429)
                  ·
                    refine ⟨540997740450657739954661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442660641201753973212429 540997740450657739954661)
                    ·
                      refine ⟨101437076334498326241499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 540997740450657739954661 101437076334498326241499)
                      ·
                        rfl

theorem cell23_197548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_197548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197548 prefixEnd_197548 := by exact prefixLift 197548
  have htrace : WordTrace (prefixWord ++ tailWord_197548) baseStart_197548 baseEnd_197548 := by
    simpa [prefixWord, tailWord_197548, baseEnd_197548] using wordTrace_append hprefix tailTrace_197548
  have hstable : (prefixWord ++ tailWord_197548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197548).length < 2 ^ (prefixWord ++ tailWord_197548).sum := by decide
  have hdescent : baseEnd_197548 < baseStart_197548 := by decide
  rcases family_descends (prefixWord ++ tailWord_197548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197578 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_197578 : Nat := 118140960795 + 197578 * 2 ^ 59
def prefixEnd_197578 : Nat := 4983230072969 + 3 ^ 40 * 197578 * 2
def baseEnd_197578 : Nat := 101452480754133208866361

theorem tailTrace_197578 : CollatzResearch.WordTrace tailWord_197578 prefixEnd_197578 101452480754133208866361 := by
  unfold tailWord_197578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801565419554031120260347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4804174452144082987360925 1801565419554031120260347)
  ·
    refine ⟨2702348129331046680390521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1801565419554031120260347 2702348129331046680390521)
    ·
      refine ⟨2026761096998285010292891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2702348129331046680390521 2026761096998285010292891)
      ·
        refine ⟨3040141645497427515439337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026761096998285010292891 3040141645497427515439337)
        ·
          refine ⟨2280106234123070636579503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3040141645497427515439337 2280106234123070636579503)
          ·
            refine ⟨3420159351184605954869255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280106234123070636579503 3420159351184605954869255)
            ·
              refine ⟨5130239026776908932303883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3420159351184605954869255 5130239026776908932303883)
              ·
                refine ⟨7695358540165363398455825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5130239026776908932303883 7695358540165363398455825)
                ·
                  refine ⟨5771518905124022548841869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7695358540165363398455825 5771518905124022548841869)
                  ·
                    refine ⟨2164319589421508455815701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5771518905124022548841869 2164319589421508455815701)
                    ·
                      refine ⟨101452480754133208866361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2164319589421508455815701 101452480754133208866361)
                      ·
                        rfl

theorem cell23_197578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_197578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197578 prefixEnd_197578 := by exact prefixLift 197578
  have htrace : WordTrace (prefixWord ++ tailWord_197578) baseStart_197578 baseEnd_197578 := by
    simpa [prefixWord, tailWord_197578, baseEnd_197578] using wordTrace_append hprefix tailTrace_197578
  have hstable : (prefixWord ++ tailWord_197578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197578).length < 2 ^ (prefixWord ++ tailWord_197578).sum := by decide
  have hdescent : baseEnd_197578 < baseStart_197578 := by decide
  rcases family_descends (prefixWord ++ tailWord_197578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197599 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 1, 4, 2]
def baseStart_197599 : Nat := 118140960795 + 197599 * 2 ^ 59
def prefixEnd_197599 : Nat := 4983230072969 + 3 ^ 40 * 197599 * 2
def baseEnd_197599 : Nat := 101463263847877626703765

theorem tailTrace_197599 : CollatzResearch.WordTrace tailWord_197599 prefixEnd_197599 101463263847877626703765 := by
  unfold tailWord_197599
  simp only [CollatzResearch.WordTrace]
  refine ⟨7207027611140045067555851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4804685074093363378370567 7207027611140045067555851)
  ·
    refine ⟨10810541416710067601333777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7207027611140045067555851 10810541416710067601333777)
    ·
      refine ⟨8107906062532550701000333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10810541416710067601333777 8107906062532550701000333)
      ·
        refine ⟨3040464773449706512875125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8107906062532550701000333 3040464773449706512875125)
        ·
          refine ⟨285043572510909985582043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3040464773449706512875125 285043572510909985582043)
          ·
            refine ⟨427565358766364978373065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285043572510909985582043 427565358766364978373065)
            ·
              refine ⟨320674019074773733779799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427565358766364978373065 320674019074773733779799)
              ·
                refine ⟨481011028612160600669699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320674019074773733779799 481011028612160600669699)
                ·
                  refine ⟨721516542918240901004549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481011028612160600669699 721516542918240901004549)
                  ·
                    refine ⟨135284351797170168938353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721516542918240901004549 135284351797170168938353)
                    ·
                      refine ⟨101463263847877626703765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135284351797170168938353 101463263847877626703765)
                      ·
                        rfl

theorem cell23_197599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_197599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197599 prefixEnd_197599 := by exact prefixLift 197599
  have htrace : WordTrace (prefixWord ++ tailWord_197599) baseStart_197599 baseEnd_197599 := by
    simpa [prefixWord, tailWord_197599, baseEnd_197599] using wordTrace_append hprefix tailTrace_197599
  have hstable : (prefixWord ++ tailWord_197599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197599).length < 2 ^ (prefixWord ++ tailWord_197599).sum := by decide
  have hdescent : baseEnd_197599 < baseStart_197599 := by decide
  rcases family_descends (prefixWord ++ tailWord_197599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197648 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 4, 8]
def baseStart_197648 : Nat := 118140960795 + 197648 * 2 ^ 59
def prefixEnd_197648 : Nat := 4983230072969 + 3 ^ 40 * 197648 * 2
def baseEnd_197648 : Nat := 33829474799982644997013

theorem tailTrace_197648 : CollatzResearch.WordTrace tailWord_197648 prefixEnd_197648 33829474799982644997013 := by
  unfold tailWord_197648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3604407393981263218044799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4805876525308350957393065 3604407393981263218044799)
  ·
    refine ⟨5406611090971894827067199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3604407393981263218044799 5406611090971894827067199)
    ·
      refine ⟨8109916636457842240600799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5406611090971894827067199 8109916636457842240600799)
      ·
        refine ⟨12164874954686763360901199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8109916636457842240600799 12164874954686763360901199)
        ·
          refine ⟨18247312432030145041351799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12164874954686763360901199 18247312432030145041351799)
          ·
            refine ⟨27370968648045217562027699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18247312432030145041351799 27370968648045217562027699)
            ·
              refine ⟨41056452972067826343041549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27370968648045217562027699 41056452972067826343041549)
              ·
                refine ⟨15396169864525434878640581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41056452972067826343041549 15396169864525434878640581)
                ·
                  refine ⟨2886781849598519039745109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15396169864525434878640581 2886781849598519039745109)
                  ·
                    refine ⟨33829474799982644997013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2886781849598519039745109 33829474799982644997013)
                    ·
                      rfl

theorem cell23_197648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_197648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197648 prefixEnd_197648 := by exact prefixLift 197648
  have htrace : WordTrace (prefixWord ++ tailWord_197648) baseStart_197648 baseEnd_197648 := by
    simpa [prefixWord, tailWord_197648, baseEnd_197648] using wordTrace_append hprefix tailTrace_197648
  have hstable : (prefixWord ++ tailWord_197648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197648).length < 2 ^ (prefixWord ++ tailWord_197648).sum := by decide
  have hdescent : baseEnd_197648 < baseStart_197648 := by decide
  rcases family_descends (prefixWord ++ tailWord_197648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197650 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_197650 : Nat := 118140960795 + 197650 * 2 ^ 59
def prefixEnd_197650 : Nat := 4983230072969 + 3 ^ 40 * 197650 * 2
def baseEnd_197650 : Nat := 101489451361256927166031

theorem tailTrace_197650 : CollatzResearch.WordTrace tailWord_197650 prefixEnd_197650 101489451361256927166031 := by
  unfold tailWord_197650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802221933488820194415601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4805925155970187185108269 1802221933488820194415601)
  ·
    refine ⟨1351666450116615145811701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1802221933488820194415601 1351666450116615145811701)
    ·
      refine ⟨126718729698432669919847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1351666450116615145811701 126718729698432669919847)
      ·
        refine ⟨190078094547649004879771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126718729698432669919847 190078094547649004879771)
        ·
          refine ⟨285117141821473507319657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190078094547649004879771 285117141821473507319657)
          ·
            refine ⟨213837856366105130489743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285117141821473507319657 213837856366105130489743)
            ·
              refine ⟨320756784549157695734615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213837856366105130489743 320756784549157695734615)
              ·
                refine ⟨481135176823736543601923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320756784549157695734615 481135176823736543601923)
                ·
                  refine ⟨721702765235604815402885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481135176823736543601923 721702765235604815402885)
                  ·
                    refine ⟨135319268481675902888041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721702765235604815402885 135319268481675902888041)
                    ·
                      refine ⟨101489451361256927166031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135319268481675902888041 101489451361256927166031)
                      ·
                        rfl

theorem cell23_197650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_197650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197650 prefixEnd_197650 := by exact prefixLift 197650
  have htrace : WordTrace (prefixWord ++ tailWord_197650) baseStart_197650 baseEnd_197650 := by
    simpa [prefixWord, tailWord_197650, baseEnd_197650] using wordTrace_append hprefix tailTrace_197650
  have hstable : (prefixWord ++ tailWord_197650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197650).length < 2 ^ (prefixWord ++ tailWord_197650).sum := by decide
  have hdescent : baseEnd_197650 < baseStart_197650 := by decide
  rcases family_descends (prefixWord ++ tailWord_197650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197675 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 3]
def baseStart_197675 : Nat := 118140960795 + 197675 * 2 ^ 59
def prefixEnd_197675 : Nat := 4983230072969 + 3 ^ 40 * 197675 * 2
def baseEnd_197675 : Nat := 101502288377619329353415

theorem tailTrace_197675 : CollatzResearch.WordTrace tailWord_197675 prefixEnd_197675 101502288377619329353415 := by
  unfold tailWord_197675
  simp only [CollatzResearch.WordTrace]
  refine ⟨7209799558864710047322479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4806533039243140031548319 7209799558864710047322479)
  ·
    refine ⟨10814699338297065070983719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7209799558864710047322479 10814699338297065070983719)
    ·
      refine ⟨16222049007445597606475579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10814699338297065070983719 16222049007445597606475579)
      ·
        refine ⟨24333073511168396409713369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16222049007445597606475579 24333073511168396409713369)
        ·
          refine ⟨18249805133376297307285027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24333073511168396409713369 18249805133376297307285027)
          ·
            refine ⟨27374707700064445960927541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18249805133376297307285027 27374707700064445960927541)
            ·
              refine ⟨2566378846881041808836957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27374707700064445960927541 2566378846881041808836957)
              ·
                refine ⟨962392067580390678313859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2566378846881041808836957 962392067580390678313859)
                ·
                  refine ⟨1443588101370586017470789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962392067580390678313859 1443588101370586017470789)
                  ·
                    refine ⟨270672769006984878275773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1443588101370586017470789 270672769006984878275773)
                    ·
                      refine ⟨101502288377619329353415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 270672769006984878275773 101502288377619329353415)
                      ·
                        rfl

theorem cell23_197675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 3].length) (baseStart_197675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197675 prefixEnd_197675 := by exact prefixLift 197675
  have htrace : WordTrace (prefixWord ++ tailWord_197675) baseStart_197675 baseEnd_197675 := by
    simpa [prefixWord, tailWord_197675, baseEnd_197675] using wordTrace_append hprefix tailTrace_197675
  have hstable : (prefixWord ++ tailWord_197675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197675).length < 2 ^ (prefixWord ++ tailWord_197675).sum := by decide
  have hdescent : baseEnd_197675 < baseStart_197675 := by decide
  rcases family_descends (prefixWord ++ tailWord_197675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197692 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_197692 : Nat := 118140960795 + 197692 * 2 ^ 59
def prefixEnd_197692 : Nat := 4983230072969 + 3 ^ 40 * 197692 * 2
def baseEnd_197692 : Nat := 101511017548745762840837

theorem tailTrace_197692 : CollatzResearch.WordTrace tailWord_197692 prefixEnd_197692 101511017548745762840837 := by
  unfold tailWord_197692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605209799901560975345665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4806946399868747967127553 3605209799901560975345665)
  ·
    refine ⟨2703907349926170731509249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3605209799901560975345665 2703907349926170731509249)
    ·
      refine ⟨2027930512444628048631937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2703907349926170731509249 2027930512444628048631937)
      ·
        refine ⟨1520947884333471036473953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2027930512444628048631937 1520947884333471036473953)
        ·
          refine ⟨1140710913250103277355465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1520947884333471036473953 1140710913250103277355465)
          ·
            refine ⟨855533184937577458016599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1140710913250103277355465 855533184937577458016599)
            ·
              refine ⟨1283299777406366187024899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855533184937577458016599 1283299777406366187024899)
              ·
                refine ⟨1924949666109549280537349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283299777406366187024899 1924949666109549280537349)
                ·
                  refine ⟨360928062395540490100753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924949666109549280537349 360928062395540490100753)
                  ·
                    refine ⟨270696046796655367575565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 360928062395540490100753 270696046796655367575565)
                    ·
                      refine ⟨101511017548745762840837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 270696046796655367575565 101511017548745762840837)
                      ·
                        rfl

theorem cell23_197692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_197692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197692 prefixEnd_197692 := by exact prefixLift 197692
  have htrace : WordTrace (prefixWord ++ tailWord_197692) baseStart_197692 baseEnd_197692 := by
    simpa [prefixWord, tailWord_197692, baseEnd_197692] using wordTrace_append hprefix tailTrace_197692
  have hstable : (prefixWord ++ tailWord_197692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197692).length < 2 ^ (prefixWord ++ tailWord_197692).sum := by decide
  have hdescent : baseEnd_197692 < baseStart_197692 := by decide
  rcases family_descends (prefixWord ++ tailWord_197692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197695 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 6]
def baseStart_197695 : Nat := 118140960795 + 197695 * 2 ^ 59
def prefixEnd_197695 : Nat := 4983230072969 + 3 ^ 40 * 197695 * 2
def baseEnd_197695 : Nat := 11279173110078805678147

theorem tailTrace_197695 : CollatzResearch.WordTrace tailWord_197695 prefixEnd_197695 11279173110078805678147 := by
  unfold tailWord_197695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7210529018792253463050539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4807019345861502308700359 7210529018792253463050539)
  ·
    refine ⟨10815793528188380194575809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7210529018792253463050539 10815793528188380194575809)
    ·
      refine ⟨8111845146141285145931857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10815793528188380194575809 8111845146141285145931857)
      ·
        refine ⟨6083883859605963859448893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8111845146141285145931857 6083883859605963859448893)
        ·
          refine ⟨2281456447352236447293335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6083883859605963859448893 2281456447352236447293335)
          ·
            refine ⟨3422184671028354670940003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281456447352236447293335 3422184671028354670940003)
            ·
              refine ⟨5133277006542532006410005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422184671028354670940003 5133277006542532006410005)
              ·
                refine ⟨240622359681681187800469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5133277006542532006410005 240622359681681187800469)
                ·
                  refine ⟨11279173110078805678147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240622359681681187800469 11279173110078805678147)
                  ·
                    rfl

theorem cell23_197695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 6].length) (baseStart_197695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197695 prefixEnd_197695 := by exact prefixLift 197695
  have htrace : WordTrace (prefixWord ++ tailWord_197695) baseStart_197695 baseEnd_197695 := by
    simpa [prefixWord, tailWord_197695, baseEnd_197695] using wordTrace_append hprefix tailTrace_197695
  have hstable : (prefixWord ++ tailWord_197695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197695).length < 2 ^ (prefixWord ++ tailWord_197695).sum := by decide
  have hdescent : baseEnd_197695 < baseStart_197695 := by decide
  rcases family_descends (prefixWord ++ tailWord_197695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197705 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 3]
def baseStart_197705 : Nat := 118140960795 + 197705 * 2 ^ 59
def prefixEnd_197705 : Nat := 4983230072969 + 3 ^ 40 * 197705 * 2
def baseEnd_197705 : Nat := 101517692797254211978277

theorem tailTrace_197705 : CollatzResearch.WordTrace tailWord_197705 prefixEnd_197705 101517692797254211978277 := by
  unfold tailWord_197705
  simp only [CollatzResearch.WordTrace]
  refine ⟨7210893748756025170914569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4807262499170683447276379 7210893748756025170914569)
  ·
    refine ⟨5408170311567018878185927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7210893748756025170914569 5408170311567018878185927)
    ·
      refine ⟨8112255467350528317278891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5408170311567018878185927 8112255467350528317278891)
      ·
        refine ⟨12168383201025792475918337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8112255467350528317278891 12168383201025792475918337)
        ·
          refine ⟨9126287400769344356938753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12168383201025792475918337 9126287400769344356938753)
          ·
            refine ⟨6844715550577008267704065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9126287400769344356938753 6844715550577008267704065)
            ·
              refine ⟨5133536662932756200778049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6844715550577008267704065 5133536662932756200778049)
              ·
                refine ⟨3850152497199567150583537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133536662932756200778049 3850152497199567150583537)
                ·
                  refine ⟨2887614372899675362937653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3850152497199567150583537 2887614372899675362937653)
                  ·
                    refine ⟨270713847459344565275405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2887614372899675362937653 270713847459344565275405)
                    ·
                      refine ⟨101517692797254211978277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 270713847459344565275405 101517692797254211978277)
                      ·
                        rfl

theorem cell23_197705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_197705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197705 prefixEnd_197705 := by exact prefixLift 197705
  have htrace : WordTrace (prefixWord ++ tailWord_197705) baseStart_197705 baseEnd_197705 := by
    simpa [prefixWord, tailWord_197705, baseEnd_197705] using wordTrace_append hprefix tailTrace_197705
  have hstable : (prefixWord ++ tailWord_197705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197705).length < 2 ^ (prefixWord ++ tailWord_197705).sum := by decide
  have hdescent : baseEnd_197705 < baseStart_197705 := by decide
  rcases family_descends (prefixWord ++ tailWord_197705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197756 : List Nat := [2, 2, 2, 1, 1, 3, 3, 4, 1, 1, 3]
def baseStart_197756 : Nat := 118140960795 + 197756 * 2 ^ 59
def prefixEnd_197756 : Nat := 4983230072969 + 3 ^ 40 * 197756 * 2
def baseEnd_197756 : Nat := 101543880310633512440543

theorem tailTrace_197756 : CollatzResearch.WordTrace tailWord_197756 prefixEnd_197756 101543880310633512440543 := by
  unfold tailWord_197756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606376935785630440510561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4808502581047507254014081 3606376935785630440510561)
  ·
    refine ⟨2704782701839222830382921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3606376935785630440510561 2704782701839222830382921)
    ·
      refine ⟨2028587026379417122787191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2704782701839222830382921 2028587026379417122787191)
      ·
        refine ⟨3042880539569125684180787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2028587026379417122787191 3042880539569125684180787)
        ·
          refine ⟨4564320809353688526271181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042880539569125684180787 4564320809353688526271181)
          ·
            refine ⟨1711620303507633197351693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4564320809353688526271181 1711620303507633197351693)
            ·
              refine ⟨641857613815362449006885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1711620303507633197351693 641857613815362449006885)
              ·
                refine ⟨120348302590380459188791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 641857613815362449006885 120348302590380459188791)
                ·
                  refine ⟨180522453885570688783187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120348302590380459188791 180522453885570688783187)
                  ·
                    refine ⟨270783680828356033174781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180522453885570688783187 270783680828356033174781)
                    ·
                      refine ⟨101543880310633512440543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 270783680828356033174781 101543880310633512440543)
                      ·
                        rfl

theorem cell23_197756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_197756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197756 prefixEnd_197756 := by exact prefixLift 197756
  have htrace : WordTrace (prefixWord ++ tailWord_197756) baseStart_197756 baseEnd_197756 := by
    simpa [prefixWord, tailWord_197756, baseEnd_197756] using wordTrace_append hprefix tailTrace_197756
  have hstable : (prefixWord ++ tailWord_197756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197756).length < 2 ^ (prefixWord ++ tailWord_197756).sum := by decide
  have hdescent : baseEnd_197756 < baseStart_197756 := by decide
  rcases family_descends (prefixWord ++ tailWord_197756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197779 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 5, 2, 2]
def baseStart_197779 : Nat := 118140960795 + 197779 * 2 ^ 59
def prefixEnd_197779 : Nat := 4983230072969 + 3 ^ 40 * 197779 * 2
def baseEnd_197779 : Nat := 101555690365686922452937

theorem tailTrace_197779 : CollatzResearch.WordTrace tailWord_197779 prefixEnd_197779 101555690365686922452937 := by
  unfold tailWord_197779
  simp only [CollatzResearch.WordTrace]
  refine ⟨7213592750487935809108391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4809061833658623872738927 7213592750487935809108391)
  ·
    refine ⟨10820389125731903713662587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7213592750487935809108391 10820389125731903713662587)
    ·
      refine ⟨16230583688597855570493881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10820389125731903713662587 16230583688597855570493881)
      ·
        refine ⟨12172937766448391677870411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16230583688597855570493881 12172937766448391677870411)
        ·
          refine ⟨18259406649672587516805617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12172937766448391677870411 18259406649672587516805617)
          ·
            refine ⟨13694554987254440637604213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18259406649672587516805617 13694554987254440637604213)
            ·
              refine ⟨1283864530055103809775395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13694554987254440637604213 1283864530055103809775395)
              ·
                refine ⟨1925796795082655714663093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283864530055103809775395 1925796795082655714663093)
                ·
                  refine ⟨180543449538998973249665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1925796795082655714663093 180543449538998973249665)
                  ·
                    refine ⟨135407587154249229937249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 180543449538998973249665 135407587154249229937249)
                    ·
                      refine ⟨101555690365686922452937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135407587154249229937249 101555690365686922452937)
                      ·
                        rfl

theorem cell23_197779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 2, 2].length) (baseStart_197779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197779 prefixEnd_197779 := by exact prefixLift 197779
  have htrace : WordTrace (prefixWord ++ tailWord_197779) baseStart_197779 baseEnd_197779 := by
    simpa [prefixWord, tailWord_197779, baseEnd_197779] using wordTrace_append hprefix tailTrace_197779
  have hstable : (prefixWord ++ tailWord_197779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197779).length < 2 ^ (prefixWord ++ tailWord_197779).sum := by decide
  have hdescent : baseEnd_197779 < baseStart_197779 := by decide
  rcases family_descends (prefixWord ++ tailWord_197779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197790 : List Nat := [4, 3, 1, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_197790 : Nat := 118140960795 + 197790 * 2 ^ 59
def prefixEnd_197790 : Nat := 4983230072969 + 3 ^ 40 * 197790 * 2
def baseEnd_197790 : Nat := 101561338652886379415387

theorem tailTrace_197790 : CollatzResearch.WordTrace tailWord_197790 prefixEnd_197790 101561338652886379415387 := by
  unfold tailWord_197790
  simp only [CollatzResearch.WordTrace]
  refine ⟨901749244181010585969853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4809329302298723125172549 901749244181010585969853)
  ·
    refine ⟨338155966567878969738695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 901749244181010585969853 338155966567878969738695)
    ·
      refine ⟨507233949851818454608043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338155966567878969738695 507233949851818454608043)
      ·
        refine ⟨760850924777727681912065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507233949851818454608043 760850924777727681912065)
        ·
          refine ⟨570638193583295761434049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760850924777727681912065 570638193583295761434049)
          ·
            refine ⟨427978645187471821075537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570638193583295761434049 427978645187471821075537)
            ·
              refine ⟨320983983890603865806653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427978645187471821075537 320983983890603865806653)
              ·
                refine ⟨120368993958976449677495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320983983890603865806653 120368993958976449677495)
                ·
                  refine ⟨180553490938464674516243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120368993958976449677495 180553490938464674516243)
                  ·
                    refine ⟨270830236407697011774365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180553490938464674516243 270830236407697011774365)
                    ·
                      refine ⟨101561338652886379415387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 270830236407697011774365 101561338652886379415387)
                      ·
                        rfl

theorem cell23_197790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_197790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197790 prefixEnd_197790 := by exact prefixLift 197790
  have htrace : WordTrace (prefixWord ++ tailWord_197790) baseStart_197790 baseEnd_197790 := by
    simpa [prefixWord, tailWord_197790, baseEnd_197790] using wordTrace_append hprefix tailTrace_197790
  have hstable : (prefixWord ++ tailWord_197790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197790).length < 2 ^ (prefixWord ++ tailWord_197790).sum := by decide
  have hdescent : baseEnd_197790 < baseStart_197790 := by decide
  rcases family_descends (prefixWord ++ tailWord_197790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197792 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_197792 : Nat := 118140960795 + 197792 * 2 ^ 59
def prefixEnd_197792 : Nat := 4983230072969 + 3 ^ 40 * 197792 * 2
def baseEnd_197792 : Nat := 101562365614195371590377

theorem tailTrace_197792 : CollatzResearch.WordTrace tailWord_197792 prefixEnd_197792 101562365614195371590377 := by
  unfold tailWord_197792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3607033449720419514665815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4809377932960559352887753 3607033449720419514665815)
  ·
    refine ⟨5410550174580629271998723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3607033449720419514665815 5410550174580629271998723)
    ·
      refine ⟨8115825261870943907998085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410550174580629271998723 8115825261870943907998085)
      ·
        refine ⟨1521717236600801982749641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8115825261870943907998085 1521717236600801982749641)
        ·
          refine ⟨1141287927450601487062231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1521717236600801982749641 1141287927450601487062231)
          ·
            refine ⟨1711931891175902230593347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141287927450601487062231 1711931891175902230593347)
            ·
              refine ⟨2567897836763853345890021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711931891175902230593347 2567897836763853345890021)
              ·
                refine ⟨481480844393222502354379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2567897836763853345890021 481480844393222502354379)
                ·
                  refine ⟨722221266589833753531569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481480844393222502354379 722221266589833753531569)
                  ·
                    refine ⟨541665949942375315148677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 722221266589833753531569 541665949942375315148677)
                    ·
                      refine ⟨101562365614195371590377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 541665949942375315148677 101562365614195371590377)
                      ·
                        rfl

theorem cell23_197792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_197792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197792 prefixEnd_197792 := by exact prefixLift 197792
  have htrace : WordTrace (prefixWord ++ tailWord_197792) baseStart_197792 baseEnd_197792 := by
    simpa [prefixWord, tailWord_197792, baseEnd_197792] using wordTrace_append hprefix tailTrace_197792
  have hstable : (prefixWord ++ tailWord_197792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197792).length < 2 ^ (prefixWord ++ tailWord_197792).sum := by decide
  have hdescent : baseEnd_197792 < baseStart_197792 := by decide
  rcases family_descends (prefixWord ++ tailWord_197792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197796 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_197796 : Nat := 118140960795 + 197796 * 2 ^ 59
def prefixEnd_197796 : Nat := 4983230072969 + 3 ^ 40 * 197796 * 2
def baseEnd_197796 : Nat := 101564419536813355940359

theorem tailTrace_197796 : CollatzResearch.WordTrace tailWord_197796 prefixEnd_197796 101564419536813355940359 := by
  unfold tailWord_197796
  simp only [CollatzResearch.WordTrace]
  refine ⟨3607106395713173856238621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4809475194284231808318161 3607106395713173856238621)
  ·
    refine ⟨1352664898392440196089483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3607106395713173856238621 1352664898392440196089483)
    ·
      refine ⟨2028997347588660294134225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1352664898392440196089483 2028997347588660294134225)
      ·
        refine ⟨1521748010691495220600669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2028997347588660294134225 1521748010691495220600669)
        ·
          refine ⟨570655504009310707725251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1521748010691495220600669 570655504009310707725251)
          ·
            refine ⟨855983256013966061587877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570655504009310707725251 855983256013966061587877)
            ·
              refine ⟨160496860502618636547727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 855983256013966061587877 160496860502618636547727)
              ·
                refine ⟨240745290753927954821591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160496860502618636547727 240745290753927954821591)
                ·
                  refine ⟨361117936130891932232387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240745290753927954821591 361117936130891932232387)
                  ·
                    refine ⟨541676904196337898348581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 361117936130891932232387 541676904196337898348581)
                    ·
                      refine ⟨101564419536813355940359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 541676904196337898348581 101564419536813355940359)
                      ·
                        rfl

theorem cell23_197796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_197796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197796 prefixEnd_197796 := by exact prefixLift 197796
  have htrace : WordTrace (prefixWord ++ tailWord_197796) baseStart_197796 baseEnd_197796 := by
    simpa [prefixWord, tailWord_197796, baseEnd_197796] using wordTrace_append hprefix tailTrace_197796
  have hstable : (prefixWord ++ tailWord_197796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197796).length < 2 ^ (prefixWord ++ tailWord_197796).sum := by decide
  have hdescent : baseEnd_197796 < baseStart_197796 := by decide
  rcases family_descends (prefixWord ++ tailWord_197796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197835 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 8]
def baseStart_197835 : Nat := 118140960795 + 197835 * 2 ^ 59
def prefixEnd_197835 : Nat := 4983230072969 + 3 ^ 40 * 197835 * 2
def baseEnd_197835 : Nat := 101584445282338703352679

theorem tailTrace_197835 : CollatzResearch.WordTrace tailWord_197835 prefixEnd_197835 101584445282338703352679 := by
  unfold tailWord_197835
  simp only [CollatzResearch.WordTrace]
  refine ⟨7215635238285057373146959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4810423492190038248764639 7215635238285057373146959)
  ·
    refine ⟨10823452857427586059720439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7215635238285057373146959 10823452857427586059720439)
    ·
      refine ⟨16235179286141379089580659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10823452857427586059720439 16235179286141379089580659)
      ·
        refine ⟨24352768929212068634370989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16235179286141379089580659 24352768929212068634370989)
        ·
          refine ⟨9132288348454525737889121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24352768929212068634370989 9132288348454525737889121)
          ·
            refine ⟨6849216261340894303416841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9132288348454525737889121 6849216261340894303416841)
            ·
              refine ⟨5136912196005670727562631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6849216261340894303416841 5136912196005670727562631)
              ·
                refine ⟨7705368294008506091343947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136912196005670727562631 7705368294008506091343947)
                ·
                  refine ⟨11558052441012759137015921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7705368294008506091343947 11558052441012759137015921)
                  ·
                    refine ⟨8668539330759569352761941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11558052441012759137015921 8668539330759569352761941)
                    ·
                      refine ⟨101584445282338703352679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 8668539330759569352761941 101584445282338703352679)
                      ·
                        rfl

theorem cell23_197835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_197835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197835 prefixEnd_197835 := by exact prefixLift 197835
  have htrace : WordTrace (prefixWord ++ tailWord_197835) baseStart_197835 baseEnd_197835 := by
    simpa [prefixWord, tailWord_197835, baseEnd_197835] using wordTrace_append hprefix tailTrace_197835
  have hstable : (prefixWord ++ tailWord_197835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197835).length < 2 ^ (prefixWord ++ tailWord_197835).sum := by decide
  have hdescent : baseEnd_197835 < baseStart_197835 := by decide
  rcases family_descends (prefixWord ++ tailWord_197835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197842 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_197842 : Nat := 118140960795 + 197842 * 2 ^ 59
def prefixEnd_197842 : Nat := 4983230072969 + 3 ^ 40 * 197842 * 2
def baseEnd_197842 : Nat := 101588039646920175965147

theorem tailTrace_197842 : CollatzResearch.WordTrace tailWord_197842 prefixEnd_197842 101588039646920175965147 := by
  unfold tailWord_197842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803972637314924392162945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4810593699506465045767853 1803972637314924392162945)
  ·
    refine ⟨1352979477986193294122209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1803972637314924392162945 1352979477986193294122209)
    ·
      refine ⟨1014734608489644970591657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1352979477986193294122209 1014734608489644970591657)
      ·
        refine ⟨761050956367233727943743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1014734608489644970591657 761050956367233727943743)
        ·
          refine ⟨1141576434550850591915615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761050956367233727943743 1141576434550850591915615)
          ·
            refine ⟨1712364651826275887873423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141576434550850591915615 1712364651826275887873423)
            ·
              refine ⟨2568546977739413831810135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712364651826275887873423 2568546977739413831810135)
              ·
                refine ⟨3852820466609120747715203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568546977739413831810135 3852820466609120747715203)
                ·
                  refine ⟨5779230699913681121572805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852820466609120747715203 5779230699913681121572805)
                  ·
                    refine ⟨1083605756233815210294901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5779230699913681121572805 1083605756233815210294901)
                    ·
                      refine ⟨101588039646920175965147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1083605756233815210294901 101588039646920175965147)
                      ·
                        rfl

theorem cell23_197842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_197842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197842 prefixEnd_197842 := by exact prefixLift 197842
  have htrace : WordTrace (prefixWord ++ tailWord_197842) baseStart_197842 baseEnd_197842 := by
    simpa [prefixWord, tailWord_197842, baseEnd_197842] using wordTrace_append hprefix tailTrace_197842
  have hstable : (prefixWord ++ tailWord_197842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197842).length < 2 ^ (prefixWord ++ tailWord_197842).sum := by decide
  have hdescent : baseEnd_197842 < baseStart_197842 := by decide
  rcases family_descends (prefixWord ++ tailWord_197842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197856 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 1, 3, 2]
def baseStart_197856 : Nat := 118140960795 + 197856 * 2 ^ 59
def prefixEnd_197856 : Nat := 4983230072969 + 3 ^ 40 * 197856 * 2
def baseEnd_197856 : Nat := 101595228376083121190083

theorem tailTrace_197856 : CollatzResearch.WordTrace tailWord_197856 prefixEnd_197856 101595228376083121190083 := by
  unfold tailWord_197856
  simp only [CollatzResearch.WordTrace]
  refine ⟨3608200585604488979830711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4810934114139318639774281 3608200585604488979830711)
  ·
    refine ⟨5412300878406733469746067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3608200585604488979830711 5412300878406733469746067)
    ·
      refine ⟨8118451317610100204619101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5412300878406733469746067 8118451317610100204619101)
      ·
        refine ⟨3044419244103787576732163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8118451317610100204619101 3044419244103787576732163)
        ·
          refine ⟨4566628866155681365098245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044419244103787576732163 4566628866155681365098245)
          ·
            refine ⟨856242912404190255955921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4566628866155681365098245 856242912404190255955921)
            ·
              refine ⟨642182184303142691966941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856242912404190255955921 642182184303142691966941)
              ·
                refine ⟨240818319113678509487603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 642182184303142691966941 240818319113678509487603)
                ·
                  refine ⟨361227478670517764231405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240818319113678509487603 361227478670517764231405)
                  ·
                    refine ⟨135460304501444161586777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 361227478670517764231405 135460304501444161586777)
                    ·
                      refine ⟨101595228376083121190083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135460304501444161586777 101595228376083121190083)
                      ·
                        rfl

theorem cell23_197856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_197856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197856 prefixEnd_197856 := by exact prefixLift 197856
  have htrace : WordTrace (prefixWord ++ tailWord_197856) baseStart_197856 baseEnd_197856 := by
    simpa [prefixWord, tailWord_197856, baseEnd_197856] using wordTrace_append hprefix tailTrace_197856
  have hstable : (prefixWord ++ tailWord_197856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197856).length < 2 ^ (prefixWord ++ tailWord_197856).sum := by decide
  have hdescent : baseEnd_197856 < baseStart_197856 := by decide
  rcases family_descends (prefixWord ++ tailWord_197856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197882 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_197882 : Nat := 118140960795 + 197882 * 2 ^ 59
def prefixEnd_197882 : Nat := 4983230072969 + 3 ^ 40 * 197882 * 2
def baseEnd_197882 : Nat := 101608578873100019464963

theorem tailTrace_197882 : CollatzResearch.WordTrace tailWord_197882 prefixEnd_197882 101608578873100019464963 := by
  unfold tailWord_197882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1804337367278696100026975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4811566312743189600071933 1804337367278696100026975)
  ·
    refine ⟨2706506050918044150040463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1804337367278696100026975 2706506050918044150040463)
    ·
      refine ⟨4059759076377066225060695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2706506050918044150040463 4059759076377066225060695)
      ·
        refine ⟨6089638614565599337591043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4059759076377066225060695 6089638614565599337591043)
        ·
          refine ⟨9134457921848399006386565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6089638614565599337591043 9134457921848399006386565)
          ·
            refine ⟨1712710860346574813697481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9134457921848399006386565 1712710860346574813697481)
            ·
              refine ⟨1284533145259931110273111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712710860346574813697481 1284533145259931110273111)
              ·
                refine ⟨1926799717889896665409667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284533145259931110273111 1926799717889896665409667)
                ·
                  refine ⟨2890199576834844998114501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926799717889896665409667 2890199576834844998114501)
                  ·
                    refine ⟨541912420656533437146469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2890199576834844998114501 541912420656533437146469)
                    ·
                      refine ⟨101608578873100019464963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 541912420656533437146469 101608578873100019464963)
                      ·
                        rfl

theorem cell23_197882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_197882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197882 prefixEnd_197882 := by exact prefixLift 197882
  have htrace : WordTrace (prefixWord ++ tailWord_197882) baseStart_197882 baseEnd_197882 := by
    simpa [prefixWord, tailWord_197882, baseEnd_197882] using wordTrace_append hprefix tailTrace_197882
  have hstable : (prefixWord ++ tailWord_197882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197882).length < 2 ^ (prefixWord ++ tailWord_197882).sum := by decide
  have hdescent : baseEnd_197882 < baseStart_197882 := by decide
  rcases family_descends (prefixWord ++ tailWord_197882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197909 : List Nat := [1, 3, 2, 1, 2, 1, 1, 7, 5]
def baseStart_197909 : Nat := 118140960795 + 197909 * 2 ^ 59
def prefixEnd_197909 : Nat := 4983230072969 + 3 ^ 40 * 197909 * 2
def baseEnd_197909 : Nat := 11291382538974601536371

theorem tailTrace_197909 : CollatzResearch.WordTrace tailWord_197909 prefixEnd_197909 11291382538974601536371 := by
  unfold tailWord_197909
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218334240016968011340781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4812222826677978674227187 7218334240016968011340781)
  ·
    refine ⟨2706875340006363004252793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7218334240016968011340781 2706875340006363004252793)
    ·
      refine ⟨2030156505004772253189595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2706875340006363004252793 2030156505004772253189595)
      ·
        refine ⟨3045234757507158379784393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030156505004772253189595 3045234757507158379784393)
        ·
          refine ⟨2283926068130368784838295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3045234757507158379784393 2283926068130368784838295)
          ·
            refine ⟨3425889102195553177257443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283926068130368784838295 3425889102195553177257443)
            ·
              refine ⟨5138833653293329765886165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425889102195553177257443 5138833653293329765886165)
              ·
                refine ⟨120441413749062416387957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5138833653293329765886165 120441413749062416387957)
                ·
                  refine ⟨11291382538974601536371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120441413749062416387957 11291382538974601536371)
                  ·
                    rfl

theorem cell23_197909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_197909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197909 prefixEnd_197909 := by exact prefixLift 197909
  have htrace : WordTrace (prefixWord ++ tailWord_197909) baseStart_197909 baseEnd_197909 := by
    simpa [prefixWord, tailWord_197909, baseEnd_197909] using wordTrace_append hprefix tailTrace_197909
  have hstable : (prefixWord ++ tailWord_197909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197909).length < 2 ^ (prefixWord ++ tailWord_197909).sum := by decide
  have hdescent : baseEnd_197909 < baseStart_197909 := by decide
  rcases family_descends (prefixWord ++ tailWord_197909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197920 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 2, 2, 2]
def baseStart_197920 : Nat := 118140960795 + 197920 * 2 ^ 59
def prefixEnd_197920 : Nat := 4983230072969 + 3 ^ 40 * 197920 * 2
def baseEnd_197920 : Nat := 101628091137970870789789

theorem tailTrace_197920 : CollatzResearch.WordTrace tailWord_197920 prefixEnd_197920 101628091137970870789789 := by
  unfold tailWord_197920
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609367721488558444995607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4812490295318077926660809 3609367721488558444995607)
  ·
    refine ⟨5414051582232837667493411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3609367721488558444995607 5414051582232837667493411)
    ·
      refine ⟨8121077373349256501240117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5414051582232837667493411 8121077373349256501240117)
      ·
        refine ⟨761351003751492796991261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8121077373349256501240117 761351003751492796991261)
        ·
          refine ⟨285506626406809798871723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 761351003751492796991261 285506626406809798871723)
          ·
            refine ⟨428259939610214698307585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285506626406809798871723 428259939610214698307585)
            ·
              refine ⟨321194954707661023730689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428259939610214698307585 321194954707661023730689)
              ·
                refine ⟨240896216030745767798017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321194954707661023730689 240896216030745767798017)
                ·
                  refine ⟨180672162023059325848513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240896216030745767798017 180672162023059325848513)
                  ·
                    refine ⟨135504121517294494386385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 180672162023059325848513 135504121517294494386385)
                    ·
                      refine ⟨101628091137970870789789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135504121517294494386385 101628091137970870789789)
                      ·
                        rfl

theorem cell23_197920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_197920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197920 prefixEnd_197920 := by exact prefixLift 197920
  have htrace : WordTrace (prefixWord ++ tailWord_197920) baseStart_197920 baseEnd_197920 := by
    simpa [prefixWord, tailWord_197920, baseEnd_197920] using wordTrace_append hprefix tailTrace_197920
  have hstable : (prefixWord ++ tailWord_197920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197920).length < 2 ^ (prefixWord ++ tailWord_197920).sum := by decide
  have hdescent : baseEnd_197920 < baseStart_197920 := by decide
  rcases family_descends (prefixWord ++ tailWord_197920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197956 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_197956 : Nat := 118140960795 + 197956 * 2 ^ 59
def prefixEnd_197956 : Nat := 4983230072969 + 3 ^ 40 * 197956 * 2
def baseEnd_197956 : Nat := 33882192147177576646541

theorem tailTrace_197956 : CollatzResearch.WordTrace tailWord_197956 prefixEnd_197956 33882192147177576646541 := by
  unfold tailWord_197956
  simp only [CollatzResearch.WordTrace]
  refine ⟨3610024235423347519150861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4813365647231130025534481 3610024235423347519150861)
  ·
    refine ⟨1353759088283755319681573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3610024235423347519150861 1353759088283755319681573)
    ·
      refine ⟨253829829053204122440295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1353759088283755319681573 253829829053204122440295)
      ·
        refine ⟨380744743579806183660443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253829829053204122440295 380744743579806183660443)
        ·
          refine ⟨571117115369709275490665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380744743579806183660443 571117115369709275490665)
          ·
            refine ⟨428337836527281956617999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571117115369709275490665 428337836527281956617999)
            ·
              refine ⟨642506754790922934926999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428337836527281956617999 642506754790922934926999)
              ·
                refine ⟨963760132186384402390499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642506754790922934926999 963760132186384402390499)
                ·
                  refine ⟨1445640198279576603585749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963760132186384402390499 1445640198279576603585749)
                  ·
                    refine ⟨33882192147177576646541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1445640198279576603585749 33882192147177576646541)
                    ·
                      rfl

theorem cell23_197956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_197956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197956 prefixEnd_197956 := by exact prefixLift 197956
  have htrace : WordTrace (prefixWord ++ tailWord_197956) baseStart_197956 baseEnd_197956 := by
    simpa [prefixWord, tailWord_197956, baseEnd_197956] using wordTrace_append hprefix tailTrace_197956
  have hstable : (prefixWord ++ tailWord_197956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197956).length < 2 ^ (prefixWord ++ tailWord_197956).sum := by decide
  have hdescent : baseEnd_197956 < baseStart_197956 := by decide
  rcases family_descends (prefixWord ++ tailWord_197956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197959 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_197959 : Nat := 118140960795 + 197959 * 2 ^ 59
def prefixEnd_197959 : Nat := 4983230072969 + 3 ^ 40 * 197959 * 2
def baseEnd_197959 : Nat := 101648116883496218202109

theorem tailTrace_197959 : CollatzResearch.WordTrace tailWord_197959 prefixEnd_197959 101648116883496218202109 := by
  unfold tailWord_197959
  simp only [CollatzResearch.WordTrace]
  refine ⟨7220157889835826550660931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4813438593223884367107287 7220157889835826550660931)
  ·
    refine ⟨10830236834753739825991397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7220157889835826550660931 10830236834753739825991397)
    ·
      refine ⟨2030669406516326217373387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10830236834753739825991397 2030669406516326217373387)
      ·
        refine ⟨3046004109774489326060081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030669406516326217373387 3046004109774489326060081)
        ·
          refine ⟨2284503082330866994545061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3046004109774489326060081 2284503082330866994545061)
          ·
            refine ⟨428344327937037561477199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2284503082330866994545061 428344327937037561477199)
            ·
              refine ⟨642516491905556342215799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428344327937037561477199 642516491905556342215799)
              ·
                refine ⟨963774737858334513323699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642516491905556342215799 963774737858334513323699)
                ·
                  refine ⟨1445662106787501769985549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963774737858334513323699 1445662106787501769985549)
                  ·
                    refine ⟨542123290045313163744581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1445662106787501769985549 542123290045313163744581)
                    ·
                      refine ⟨101648116883496218202109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 542123290045313163744581 101648116883496218202109)
                      ·
                        rfl

theorem cell23_197959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_197959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197959 prefixEnd_197959 := by exact prefixLift 197959
  have htrace : WordTrace (prefixWord ++ tailWord_197959) baseStart_197959 baseEnd_197959 := by
    simpa [prefixWord, tailWord_197959, baseEnd_197959] using wordTrace_append hprefix tailTrace_197959
  have hstable : (prefixWord ++ tailWord_197959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197959).length < 2 ^ (prefixWord ++ tailWord_197959).sum := by decide
  have hdescent : baseEnd_197959 < baseStart_197959 := by decide
  rcases family_descends (prefixWord ++ tailWord_197959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197969 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 5, 4]
def baseStart_197969 : Nat := 118140960795 + 197969 * 2 ^ 59
def prefixEnd_197969 : Nat := 4983230072969 + 3 ^ 40 * 197969 * 2
def baseEnd_197969 : Nat := 33884417230013726359021

theorem tailTrace_197969 : CollatzResearch.WordTrace tailWord_197969 prefixEnd_197969 33884417230013726359021 := by
  unfold tailWord_197969
  simp only [CollatzResearch.WordTrace]
  refine ⟨7220522619799598258524961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4813681746533065505683307 7220522619799598258524961)
  ·
    refine ⟨5415391964849698693893721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7220522619799598258524961 5415391964849698693893721)
    ·
      refine ⟨4061543973637274020420291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5415391964849698693893721 4061543973637274020420291)
      ·
        refine ⟨6092315960455911030630437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061543973637274020420291 6092315960455911030630437)
        ·
          refine ⟨1142309242585483318243207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6092315960455911030630437 1142309242585483318243207)
          ·
            refine ⟨1713463863878224977364811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142309242585483318243207 1713463863878224977364811)
            ·
              refine ⟨2570195795817337466047217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713463863878224977364811 2570195795817337466047217)
              ·
                refine ⟨1927646846863003099535413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570195795817337466047217 1927646846863003099535413)
                ·
                  refine ⟨180716891893406540581445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1927646846863003099535413 180716891893406540581445)
                  ·
                    refine ⟨33884417230013726359021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 180716891893406540581445 33884417230013726359021)
                    ·
                      rfl

theorem cell23_197969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_197969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_197969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_197969 prefixEnd_197969 := by exact prefixLift 197969
  have htrace : WordTrace (prefixWord ++ tailWord_197969) baseStart_197969 baseEnd_197969 := by
    simpa [prefixWord, tailWord_197969, baseEnd_197969] using wordTrace_append hprefix tailTrace_197969
  have hstable : (prefixWord ++ tailWord_197969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197969).length < 2 ^ (prefixWord ++ tailWord_197969).sum := by decide
  have hdescent : baseEnd_197969 < baseStart_197969 := by decide
  rcases family_descends (prefixWord ++ tailWord_197969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198020 : List Nat := [2, 3, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_198020 : Nat := 118140960795 + 198020 * 2 ^ 59
def prefixEnd_198020 : Nat := 4983230072969 + 3 ^ 40 * 198020 * 2
def baseEnd_198020 : Nat := 33893146401140159846443

theorem tailTrace_198020 : CollatzResearch.WordTrace tailWord_198020 prefixEnd_198020 33893146401140159846443 := by
  unfold tailWord_198020
  simp only [CollatzResearch.WordTrace]
  refine ⟨3611191371307416984315757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4814921828409889312421009 3611191371307416984315757)
  ·
    refine ⟨1354196764240281369118409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3611191371307416984315757 1354196764240281369118409)
    ·
      refine ⟨1015647573180211026838807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1354196764240281369118409 1015647573180211026838807)
      ·
        refine ⟨1523471359770316540258211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015647573180211026838807 1523471359770316540258211)
        ·
          refine ⟨2285207039655474810387317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523471359770316540258211 2285207039655474810387317)
          ·
            refine ⟨214238159967700763473811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2285207039655474810387317 214238159967700763473811)
            ·
              refine ⟨321357239951551145210717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214238159967700763473811 321357239951551145210717)
              ·
                refine ⟨120508964981831679454019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321357239951551145210717 120508964981831679454019)
                ·
                  refine ⟨180763447472747519181029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120508964981831679454019 180763447472747519181029)
                  ·
                    refine ⟨33893146401140159846443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 180763447472747519181029 33893146401140159846443)
                    ·
                      rfl

theorem cell23_198020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_198020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198020 prefixEnd_198020 := by exact prefixLift 198020
  have htrace : WordTrace (prefixWord ++ tailWord_198020) baseStart_198020 baseEnd_198020 := by
    simpa [prefixWord, tailWord_198020, baseEnd_198020] using wordTrace_append hprefix tailTrace_198020
  have hstable : (prefixWord ++ tailWord_198020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198020).length < 2 ^ (prefixWord ++ tailWord_198020).sum := by decide
  have hdescent : baseEnd_198020 < baseStart_198020 := by decide
  rcases family_descends (prefixWord ++ tailWord_198020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198066 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_198066 : Nat := 118140960795 + 198066 * 2 ^ 59
def prefixEnd_198066 : Nat := 4983230072969 + 3 ^ 40 * 198066 * 2
def baseEnd_198066 : Nat := 101703059313527299564117

theorem tailTrace_198066 : CollatzResearch.WordTrace tailWord_198066 prefixEnd_198066 101703059313527299564117 := by
  unfold tailWord_198066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806015125112045956201513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4816040333632122549870701 1806015125112045956201513)
  ·
    refine ⟨1354511343834034467151135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1806015125112045956201513 1354511343834034467151135)
    ·
      refine ⟨2031767015751051700726703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1354511343834034467151135 2031767015751051700726703)
      ·
        refine ⟨3047650523626577551090055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031767015751051700726703 3047650523626577551090055)
        ·
          refine ⟨4571475785439866326635083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047650523626577551090055 4571475785439866326635083)
          ·
            refine ⟨6857213678159799489952625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571475785439866326635083 6857213678159799489952625)
            ·
              refine ⟨5142910258619849617464469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6857213678159799489952625 5142910258619849617464469)
              ·
                refine ⟨241073918372805450818647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5142910258619849617464469 241073918372805450818647)
                ·
                  refine ⟨361610877559208176227971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241073918372805450818647 361610877559208176227971)
                  ·
                    refine ⟨542416316338812264341957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 361610877559208176227971 542416316338812264341957)
                    ·
                      refine ⟨101703059313527299564117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 542416316338812264341957 101703059313527299564117)
                      ·
                        rfl

theorem cell23_198066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_198066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198066 prefixEnd_198066 := by exact prefixLift 198066
  have htrace : WordTrace (prefixWord ++ tailWord_198066) baseStart_198066 baseEnd_198066 := by
    simpa [prefixWord, tailWord_198066, baseEnd_198066] using wordTrace_append hprefix tailTrace_198066
  have hstable : (prefixWord ++ tailWord_198066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198066).length < 2 ^ (prefixWord ++ tailWord_198066).sum := by decide
  have hdescent : baseEnd_198066 < baseStart_198066 := by decide
  rcases family_descends (prefixWord ++ tailWord_198066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198106 : List Nat := [3, 1, 1, 2, 3, 4, 1, 8]
def baseStart_198106 : Nat := 118140960795 + 198106 * 2 ^ 59
def prefixEnd_198106 : Nat := 4983230072969 + 3 ^ 40 * 198106 * 2
def baseEnd_198106 : Nat := 3767540686655820113479

theorem tailTrace_198106 : CollatzResearch.WordTrace tailWord_198106 prefixEnd_198106 3767540686655820113479 := by
  unfold tailWord_198106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806379855075817664065543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4817012946868847104174781 1806379855075817664065543)
  ·
    refine ⟨2709569782613726496098315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1806379855075817664065543 2709569782613726496098315)
    ·
      refine ⟨4064354673920589744147473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2709569782613726496098315 4064354673920589744147473)
      ·
        refine ⟨3048266005440442308110605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4064354673920589744147473 3048266005440442308110605)
        ·
          refine ⟨1143099752040165865541477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3048266005440442308110605 1143099752040165865541477)
          ·
            refine ⟨214331203507531099789027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1143099752040165865541477 214331203507531099789027)
            ·
              refine ⟨321496805261296649683541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214331203507531099789027 321496805261296649683541)
              ·
                refine ⟨3767540686655820113479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 321496805261296649683541 3767540686655820113479)
                ·
                  rfl

theorem cell23_198106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 8].length) (baseStart_198106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198106 prefixEnd_198106 := by exact prefixLift 198106
  have htrace : WordTrace (prefixWord ++ tailWord_198106) baseStart_198106 baseEnd_198106 := by
    simpa [prefixWord, tailWord_198106, baseEnd_198106] using wordTrace_append hprefix tailTrace_198106
  have hstable : (prefixWord ++ tailWord_198106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198106).length < 2 ^ (prefixWord ++ tailWord_198106).sum := by decide
  have hdescent : baseEnd_198106 < baseStart_198106 := by decide
  rcases family_descends (prefixWord ++ tailWord_198106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198134 : List Nat := [5, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_198134 : Nat := 118140960795 + 198134 * 2 ^ 59
def prefixEnd_198134 : Nat := 4983230072969 + 3 ^ 40 * 198134 * 2
def baseEnd_198134 : Nat := 101737975998033033513805

theorem tailTrace_198134 : CollatzResearch.WordTrace tailWord_198134 prefixEnd_198134 101737975998033033513805 := by
  unfold tailWord_198134
  simp only [CollatzResearch.WordTrace]
  refine ⟨451658791512614464892591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4817693776134554292187637 451658791512614464892591)
  ·
    refine ⟨677488187268921697338887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 451658791512614464892591 677488187268921697338887)
    ·
      refine ⟨1016232280903382546008331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677488187268921697338887 1016232280903382546008331)
      ·
        refine ⟨1524348421355073819012497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016232280903382546008331 1524348421355073819012497)
        ·
          refine ⟨1143261316016305364259373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1524348421355073819012497 1143261316016305364259373)
          ·
            refine ⟨428722993506114511597265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1143261316016305364259373 428722993506114511597265)
            ·
              refine ⟨321542245129585883697949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428722993506114511597265 321542245129585883697949)
              ·
                refine ⟨120578341923594706386731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321542245129585883697949 120578341923594706386731)
                ·
                  refine ⟨180867512885392059580097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120578341923594706386731 180867512885392059580097)
                  ·
                    refine ⟨135650634664044044685073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 180867512885392059580097 135650634664044044685073)
                    ·
                      refine ⟨101737975998033033513805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135650634664044044685073 101737975998033033513805)
                      ·
                        rfl

theorem cell23_198134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_198134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198134 prefixEnd_198134 := by exact prefixLift 198134
  have htrace : WordTrace (prefixWord ++ tailWord_198134) baseStart_198134 baseEnd_198134 := by
    simpa [prefixWord, tailWord_198134, baseEnd_198134] using wordTrace_append hprefix tailTrace_198134
  have hstable : (prefixWord ++ tailWord_198134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198134).length < 2 ^ (prefixWord ++ tailWord_198134).sum := by decide
  have hdescent : baseEnd_198134 < baseStart_198134 := by decide
  rcases family_descends (prefixWord ++ tailWord_198134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198139 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 4]
def baseStart_198139 : Nat := 118140960795 + 198139 * 2 ^ 59
def prefixEnd_198139 : Nat := 4983230072969 + 3 ^ 40 * 198139 * 2
def baseEnd_198139 : Nat := 101740543401305513951281

theorem tailTrace_198139 : CollatzResearch.WordTrace tailWord_198139 prefixEnd_198139 101740543401305513951281 := by
  unfold tailWord_198139
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226723029183717292213471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4817815352789144861475647 7226723029183717292213471)
  ·
    refine ⟨10840084543775575938320207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7226723029183717292213471 10840084543775575938320207)
    ·
      refine ⟨16260126815663363907480311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10840084543775575938320207 16260126815663363907480311)
      ·
        refine ⟨24390190223495045861220467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16260126815663363907480311 24390190223495045861220467)
        ·
          refine ⟨36585285335242568791830701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24390190223495045861220467 36585285335242568791830701)
          ·
            refine ⟨13719482000715963296936513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36585285335242568791830701 13719482000715963296936513)
            ·
              refine ⟨10289611500536972472702385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13719482000715963296936513 10289611500536972472702385)
              ·
                refine ⟨7717208625402729354526789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10289611500536972472702385 7717208625402729354526789)
                ·
                  refine ⟨1446976617263011753973773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7717208625402729354526789 1446976617263011753973773)
                  ·
                    refine ⟨542616231473629407740165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1446976617263011753973773 542616231473629407740165)
                    ·
                      refine ⟨101740543401305513951281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 542616231473629407740165 101740543401305513951281)
                      ·
                        rfl

theorem cell23_198139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 4].length) (baseStart_198139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198139 prefixEnd_198139 := by exact prefixLift 198139
  have htrace : WordTrace (prefixWord ++ tailWord_198139) baseStart_198139 baseEnd_198139 := by
    simpa [prefixWord, tailWord_198139, baseEnd_198139] using wordTrace_append hprefix tailTrace_198139
  have hstable : (prefixWord ++ tailWord_198139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198139).length < 2 ^ (prefixWord ++ tailWord_198139).sum := by decide
  have hdescent : baseEnd_198139 < baseStart_198139 := by decide
  rcases family_descends (prefixWord ++ tailWord_198139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198174 : List Nat := [4, 3, 3, 1, 1, 2, 2, 7]
def baseStart_198174 : Nat := 118140960795 + 198174 * 2 ^ 59
def prefixEnd_198174 : Nat := 4983230072969 + 3 ^ 40 * 198174 * 2
def baseEnd_198174 : Nat := 3768833897193069519023

theorem tailTrace_198174 : CollatzResearch.WordTrace tailWord_198174 prefixEnd_198174 3768833897193069519023 := by
  unfold tailWord_198174
  simp only [CollatzResearch.WordTrace]
  refine ⟨903499948007114783717197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4818666389371278846491717 903499948007114783717197)
  ·
    refine ⟨338812480502668043893949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 903499948007114783717197 338812480502668043893949)
    ·
      refine ⟨127054680188500516460231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338812480502668043893949 127054680188500516460231)
      ·
        refine ⟨190582020282750774690347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127054680188500516460231 190582020282750774690347)
        ·
          refine ⟨285873030424126162035521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190582020282750774690347 285873030424126162035521)
          ·
            refine ⟨214404772818094621526641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285873030424126162035521 214404772818094621526641)
            ·
              refine ⟨160803579613570966144981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214404772818094621526641 160803579613570966144981)
              ·
                refine ⟨3768833897193069519023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160803579613570966144981 3768833897193069519023)
                ·
                  rfl

theorem cell23_198174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_198174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198174 prefixEnd_198174 := by exact prefixLift 198174
  have htrace : WordTrace (prefixWord ++ tailWord_198174) baseStart_198174 baseEnd_198174 := by
    simpa [prefixWord, tailWord_198174, baseEnd_198174] using wordTrace_append hprefix tailTrace_198174
  have hstable : (prefixWord ++ tailWord_198174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198174).length < 2 ^ (prefixWord ++ tailWord_198174).sum := by decide
  have hdescent : baseEnd_198174 < baseStart_198174 := by decide
  rcases family_descends (prefixWord ++ tailWord_198174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198243 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 2, 5]
def baseStart_198243 : Nat := 118140960795 + 198243 * 2 ^ 59
def prefixEnd_198243 : Nat := 4983230072969 + 3 ^ 40 * 198243 * 2
def baseEnd_198243 : Nat := 33931315129791035683601

theorem tailTrace_198243 : CollatzResearch.WordTrace tailWord_198243 prefixEnd_198243 33931315129791035683601 := by
  unfold tailWord_198243
  simp only [CollatzResearch.WordTrace]
  refine ⟨7230516220806943053999383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4820344147204628702666255 7230516220806943053999383)
  ·
    refine ⟨10845774331210414580999075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7230516220806943053999383 10845774331210414580999075)
    ·
      refine ⟨16268661496815621871498613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10845774331210414580999075 16268661496815621871498613)
      ·
        refine ⟨1525187015326464550452995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16268661496815621871498613 1525187015326464550452995)
        ·
          refine ⟨2287780522989696825679493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525187015326464550452995 2287780522989696825679493)
          ·
            refine ⟨428958848060568154814905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2287780522989696825679493 428958848060568154814905)
            ·
              refine ⟨321719136045426116111179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428958848060568154814905 321719136045426116111179)
              ·
                refine ⟨482578704068139174166769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321719136045426116111179 482578704068139174166769)
                ·
                  refine ⟨361934028051104380625077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482578704068139174166769 361934028051104380625077)
                  ·
                    refine ⟨33931315129791035683601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 361934028051104380625077 33931315129791035683601)
                    ·
                      rfl

theorem cell23_198243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 5].length) (baseStart_198243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198243 prefixEnd_198243 := by exact prefixLift 198243
  have htrace : WordTrace (prefixWord ++ tailWord_198243) baseStart_198243 baseEnd_198243 := by
    simpa [prefixWord, tailWord_198243, baseEnd_198243] using wordTrace_append hprefix tailTrace_198243
  have hstable : (prefixWord ++ tailWord_198243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198243).length < 2 ^ (prefixWord ++ tailWord_198243).sum := by decide
  have hdescent : baseEnd_198243 < baseStart_198243 := by decide
  rcases family_descends (prefixWord ++ tailWord_198243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198263 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 2, 4, 2]
def baseStart_198263 : Nat := 118140960795 + 198263 * 2 ^ 59
def prefixEnd_198263 : Nat := 4983230072969 + 3 ^ 40 * 198263 * 2
def baseEnd_198263 : Nat := 101804215002463028800711

theorem tailTrace_198263 : CollatzResearch.WordTrace tailWord_198263 prefixEnd_198263 101804215002463028800711 := by
  unfold tailWord_198263
  simp only [CollatzResearch.WordTrace]
  refine ⟨7231245680734486469727443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4820830453822990979818295 7231245680734486469727443)
  ·
    refine ⟨10846868521101729704591165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7231245680734486469727443 10846868521101729704591165)
    ·
      refine ⟨4067575695413148639221687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10846868521101729704591165 4067575695413148639221687)
      ·
        refine ⟨6101363543119722958832531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067575695413148639221687 6101363543119722958832531)
        ·
          refine ⟨9152045314679584438248797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6101363543119722958832531 9152045314679584438248797)
          ·
            refine ⟨3432016993004844164343299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9152045314679584438248797 3432016993004844164343299)
            ·
              refine ⟨5148025489507266246514949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432016993004844164343299 5148025489507266246514949)
              ·
                refine ⟨965254779282612421221553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5148025489507266246514949 965254779282612421221553)
                ·
                  refine ⟨723941084461959315916165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 965254779282612421221553 723941084461959315916165)
                  ·
                    refine ⟨135738953336617371734281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 723941084461959315916165 135738953336617371734281)
                    ·
                      refine ⟨101804215002463028800711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135738953336617371734281 101804215002463028800711)
                      ·
                        rfl

theorem cell23_198263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_198263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198263 prefixEnd_198263 := by exact prefixLift 198263
  have htrace : WordTrace (prefixWord ++ tailWord_198263) baseStart_198263 baseEnd_198263 := by
    simpa [prefixWord, tailWord_198263, baseEnd_198263] using wordTrace_append hprefix tailTrace_198263
  have hstable : (prefixWord ++ tailWord_198263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198263).length < 2 ^ (prefixWord ++ tailWord_198263).sum := by decide
  have hdescent : baseEnd_198263 < baseStart_198263 := by decide
  rcases family_descends (prefixWord ++ tailWord_198263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198300 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_198300 : Nat := 118140960795 + 198300 * 2 ^ 59
def prefixEnd_198300 : Nat := 4983230072969 + 3 ^ 40 * 198300 * 2
def baseEnd_198300 : Nat := 101823213786679384038041

theorem tailTrace_198300 : CollatzResearch.WordTrace tailWord_198300 prefixEnd_198300 101823213786679384038041 := by
  unfold tailWord_198300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3616297590800220894412177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4821730121066961192549569 3616297590800220894412177)
  ·
    refine ⟨2712223193100165670809133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3616297590800220894412177 2712223193100165670809133)
    ·
      refine ⟨1017083697412562126553425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2712223193100165670809133 1017083697412562126553425)
      ·
        refine ⟨762812773059421594915069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1017083697412562126553425 762812773059421594915069)
        ·
          refine ⟨286054789897283098093151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 762812773059421594915069 286054789897283098093151)
          ·
            refine ⟨429082184845924647139727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286054789897283098093151 429082184845924647139727)
            ·
              refine ⟨643623277268886970709591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429082184845924647139727 643623277268886970709591)
              ·
                refine ⟨965434915903330456064387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643623277268886970709591 965434915903330456064387)
                ·
                  refine ⟨1448152373854995684096581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965434915903330456064387 1448152373854995684096581)
                  ·
                    refine ⟨271528570097811690768109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1448152373854995684096581 271528570097811690768109)
                    ·
                      refine ⟨101823213786679384038041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 271528570097811690768109 101823213786679384038041)
                      ·
                        rfl

theorem cell23_198300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_198300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198300 prefixEnd_198300 := by exact prefixLift 198300
  have htrace : WordTrace (prefixWord ++ tailWord_198300) baseStart_198300 baseEnd_198300 := by
    simpa [prefixWord, tailWord_198300, baseEnd_198300] using wordTrace_append hprefix tailTrace_198300
  have hstable : (prefixWord ++ tailWord_198300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198300).length < 2 ^ (prefixWord ++ tailWord_198300).sum := by decide
  have hdescent : baseEnd_198300 < baseStart_198300 := by decide
  rcases family_descends (prefixWord ++ tailWord_198300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198330 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3]
def baseStart_198330 : Nat := 118140960795 + 198330 * 2 ^ 59
def prefixEnd_198330 : Nat := 4983230072969 + 3 ^ 40 * 198330 * 2
def baseEnd_198330 : Nat := 101838618206314266662903

theorem tailTrace_198330 : CollatzResearch.WordTrace tailWord_198330 prefixEnd_198330 101838618206314266662903 := by
  unfold tailWord_198330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808422342872939228104111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4822459580994504608277629 1808422342872939228104111)
  ·
    refine ⟨2712633514309408842156167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1808422342872939228104111 2712633514309408842156167)
    ·
      refine ⟨4068950271464113263234251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2712633514309408842156167 4068950271464113263234251)
      ·
        refine ⟨6103425407196169894851377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068950271464113263234251 6103425407196169894851377)
        ·
          refine ⟨4577569055397127421138533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6103425407196169894851377 4577569055397127421138533)
          ·
            refine ⟨858294197886961391463475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4577569055397127421138533 858294197886961391463475)
            ·
              refine ⟨1287441296830442087195213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858294197886961391463475 1287441296830442087195213)
              ·
                refine ⟨482790486311415782698205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1287441296830442087195213 482790486311415782698205)
                ·
                  refine ⟨181046432366780918511827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482790486311415782698205 181046432366780918511827)
                  ·
                    refine ⟨271569648550171377767741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181046432366780918511827 271569648550171377767741)
                    ·
                      refine ⟨101838618206314266662903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 271569648550171377767741 101838618206314266662903)
                      ·
                        rfl

theorem cell23_198330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_198330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198330 prefixEnd_198330 := by exact prefixLift 198330
  have htrace : WordTrace (prefixWord ++ tailWord_198330) baseStart_198330 baseEnd_198330 := by
    simpa [prefixWord, tailWord_198330, baseEnd_198330] using wordTrace_append hprefix tailTrace_198330
  have hstable : (prefixWord ++ tailWord_198330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198330).length < 2 ^ (prefixWord ++ tailWord_198330).sum := by decide
  have hdescent : baseEnd_198330 < baseStart_198330 := by decide
  rcases family_descends (prefixWord ++ tailWord_198330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198340 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_198340 : Nat := 118140960795 + 198340 * 2 ^ 59
def prefixEnd_198340 : Nat := 4983230072969 + 3 ^ 40 * 198340 * 2
def baseEnd_198340 : Nat := 101843753012859227537857

theorem tailTrace_198340 : CollatzResearch.WordTrace tailWord_198340 prefixEnd_198340 101843753012859227537857 := by
  unfold tailWord_198340
  simp only [CollatzResearch.WordTrace]
  refine ⟨3617027050727764310140237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4822702734303685746853649 3617027050727764310140237)
  ·
    refine ⟨1356385144022911616302589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3617027050727764310140237 1356385144022911616302589)
    ·
      refine ⟨508644429008591856113471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1356385144022911616302589 508644429008591856113471)
      ·
        refine ⟨762966643512887784170207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508644429008591856113471 762966643512887784170207)
        ·
          refine ⟨1144449965269331676255311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762966643512887784170207 1144449965269331676255311)
          ·
            refine ⟨1716674947903997514382967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144449965269331676255311 1716674947903997514382967)
            ·
              refine ⟨2575012421855996271574451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716674947903997514382967 2575012421855996271574451)
              ·
                refine ⟨3862518632783994407361677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575012421855996271574451 3862518632783994407361677)
                ·
                  refine ⟨1448444487293997902760629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3862518632783994407361677 1448444487293997902760629)
                  ·
                    refine ⟨135791670683812303383809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1448444487293997902760629 135791670683812303383809)
                    ·
                      refine ⟨101843753012859227537857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135791670683812303383809 101843753012859227537857)
                      ·
                        rfl

theorem cell23_198340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_198340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198340 prefixEnd_198340 := by exact prefixLift 198340
  have htrace : WordTrace (prefixWord ++ tailWord_198340) baseStart_198340 baseEnd_198340 := by
    simpa [prefixWord, tailWord_198340, baseEnd_198340] using wordTrace_append hprefix tailTrace_198340
  have hstable : (prefixWord ++ tailWord_198340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198340).length < 2 ^ (prefixWord ++ tailWord_198340).sum := by decide
  have hdescent : baseEnd_198340 < baseStart_198340 := by decide
  rcases family_descends (prefixWord ++ tailWord_198340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198350 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_198350 : Nat := 118140960795 + 198350 * 2 ^ 59
def prefixEnd_198350 : Nat := 4983230072969 + 3 ^ 40 * 198350 * 2
def baseEnd_198350 : Nat := 33949629273134729470937

theorem tailTrace_198350 : CollatzResearch.WordTrace tailWord_198350 prefixEnd_198350 33949629273134729470937 := by
  unfold tailWord_198350
  simp only [CollatzResearch.WordTrace]
  refine ⟨904302353927412541018063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4822945887612866885429669 904302353927412541018063)
  ·
    refine ⟨1356453530891118811527095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 904302353927412541018063 1356453530891118811527095)
    ·
      refine ⟨2034680296336678217290643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356453530891118811527095 2034680296336678217290643)
      ·
        refine ⟨3052020444505017325935965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2034680296336678217290643 3052020444505017325935965)
        ·
          refine ⟨1144507666689381497225987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3052020444505017325935965 1144507666689381497225987)
          ·
            refine ⟨1716761500034072245838981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144507666689381497225987 1716761500034072245838981)
            ·
              refine ⟨321892781256388546094809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1716761500034072245838981 321892781256388546094809)
              ·
                refine ⟨241419585942291409571107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321892781256388546094809 241419585942291409571107)
                ·
                  refine ⟨362129378913437114356661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241419585942291409571107 362129378913437114356661)
                  ·
                    refine ⟨33949629273134729470937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 362129378913437114356661 33949629273134729470937)
                    ·
                      rfl

theorem cell23_198350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_198350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198350 prefixEnd_198350 := by exact prefixLift 198350
  have htrace : WordTrace (prefixWord ++ tailWord_198350) baseStart_198350 baseEnd_198350 := by
    simpa [prefixWord, tailWord_198350, baseEnd_198350] using wordTrace_append hprefix tailTrace_198350
  have hstable : (prefixWord ++ tailWord_198350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198350).length < 2 ^ (prefixWord ++ tailWord_198350).sum := by decide
  have hdescent : baseEnd_198350 < baseStart_198350 := by decide
  rcases family_descends (prefixWord ++ tailWord_198350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198358 : List Nat := [5, 2, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_198358 : Nat := 118140960795 + 198358 * 2 ^ 59
def prefixEnd_198358 : Nat := 4983230072969 + 3 ^ 40 * 198358 * 2
def baseEnd_198358 : Nat := 33950998554880052370925

theorem tailTrace_198358 : CollatzResearch.WordTrace tailWord_198358 prefixEnd_198358 33950998554880052370925 := by
  unfold tailWord_198358
  simp only [CollatzResearch.WordTrace]
  refine ⟨452169413461894855902233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4823140410260211796290485 452169413461894855902233)
  ·
    refine ⟨339127060096421141926675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 452169413461894855902233 339127060096421141926675)
    ·
      refine ⟨508690590144631712890013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339127060096421141926675 508690590144631712890013)
      ·
        refine ⟨190758971304236892333755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 508690590144631712890013 190758971304236892333755)
        ·
          refine ⟨286138456956355338500633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190758971304236892333755 286138456956355338500633)
          ·
            refine ⟨214603842717266503875475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286138456956355338500633 214603842717266503875475)
            ·
              refine ⟨321905764075899755813213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214603842717266503875475 321905764075899755813213)
              ·
                refine ⟨120714661528462408429955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321905764075899755813213 120714661528462408429955)
                ·
                  refine ⟨181071992292693612644933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120714661528462408429955 181071992292693612644933)
                  ·
                    refine ⟨33950998554880052370925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181071992292693612644933 33950998554880052370925)
                    ·
                      rfl

theorem cell23_198358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_198358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198358 prefixEnd_198358 := by exact prefixLift 198358
  have htrace : WordTrace (prefixWord ++ tailWord_198358) baseStart_198358 baseEnd_198358 := by
    simpa [prefixWord, tailWord_198358, baseEnd_198358] using wordTrace_append hprefix tailTrace_198358
  have hstable : (prefixWord ++ tailWord_198358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198358).length < 2 ^ (prefixWord ++ tailWord_198358).sum := by decide
  have hdescent : baseEnd_198358 < baseStart_198358 := by decide
  rcases family_descends (prefixWord ++ tailWord_198358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198381 : List Nat := [1, 5, 1, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_198381 : Nat := 118140960795 + 198381 * 2 ^ 59
def prefixEnd_198381 : Nat := 4983230072969 + 3 ^ 40 * 198381 * 2
def baseEnd_198381 : Nat := 101864805719693567125169

theorem tailTrace_198381 : CollatzResearch.WordTrace tailWord_198381 prefixEnd_198381 101864805719693567125169 := by
  unfold tailWord_198381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7235549494306992622522997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4823699662871328415015331 7235549494306992622522997)
  ·
    refine ⟨678332765091280558361531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7235549494306992622522997 678332765091280558361531)
    ·
      refine ⟨1017499147636920837542297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 678332765091280558361531 1017499147636920837542297)
      ·
        refine ⟨763124360727690628156723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1017499147636920837542297 763124360727690628156723)
        ·
          refine ⟨1144686541091535942235085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763124360727690628156723 1144686541091535942235085)
          ·
            refine ⟨429257452909325978338157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1144686541091535942235085 429257452909325978338157)
            ·
              refine ⟨160971544840997241876809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429257452909325978338157 160971544840997241876809)
              ·
                refine ⟨120728658630747931407607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160971544840997241876809 120728658630747931407607)
                ·
                  refine ⟨181092987946121897111411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120728658630747931407607 181092987946121897111411)
                  ·
                    refine ⟨271639481919182845667117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181092987946121897111411 271639481919182845667117)
                    ·
                      refine ⟨101864805719693567125169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 271639481919182845667117 101864805719693567125169)
                      ·
                        rfl

theorem cell23_198381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_198381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198381 prefixEnd_198381 := by exact prefixLift 198381
  have htrace : WordTrace (prefixWord ++ tailWord_198381) baseStart_198381 baseEnd_198381 := by
    simpa [prefixWord, tailWord_198381, baseEnd_198381] using wordTrace_append hprefix tailTrace_198381
  have hstable : (prefixWord ++ tailWord_198381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198381).length < 2 ^ (prefixWord ++ tailWord_198381).sum := by decide
  have hdescent : baseEnd_198381 < baseStart_198381 := by decide
  rcases family_descends (prefixWord ++ tailWord_198381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198387 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 3, 2, 2]
def baseStart_198387 : Nat := 118140960795 + 198387 * 2 ^ 59
def prefixEnd_198387 : Nat := 4983230072969 + 3 ^ 40 * 198387 * 2
def baseEnd_198387 : Nat := 101867886603620543650141

theorem tailTrace_198387 : CollatzResearch.WordTrace tailWord_198387 prefixEnd_198387 101867886603620543650141 := by
  unfold tailWord_198387
  simp only [CollatzResearch.WordTrace]
  refine ⟨7235768332285255647241415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4823845554856837098160943 7235768332285255647241415)
  ·
    refine ⟨10853652498427883470862123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7235768332285255647241415 10853652498427883470862123)
    ·
      refine ⟨16280478747641825206293185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10853652498427883470862123 16280478747641825206293185)
      ·
        refine ⟨12210359060731368904719889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16280478747641825206293185 12210359060731368904719889)
        ·
          refine ⟨9157769295548526678539917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12210359060731368904719889 9157769295548526678539917)
          ·
            refine ⟨3434163485830697504452469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9157769295548526678539917 3434163485830697504452469)
            ·
              refine ⟨321952826796627891042419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3434163485830697504452469 321952826796627891042419)
              ·
                refine ⟨482929240194941836563629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321952826796627891042419 482929240194941836563629)
                ·
                  refine ⟨181098465073103188711361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482929240194941836563629 181098465073103188711361)
                  ·
                    refine ⟨135823848804827391533521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181098465073103188711361 135823848804827391533521)
                    ·
                      refine ⟨101867886603620543650141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135823848804827391533521 101867886603620543650141)
                      ·
                        rfl

theorem cell23_198387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 2, 2].length) (baseStart_198387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198387 prefixEnd_198387 := by exact prefixLift 198387
  have htrace : WordTrace (prefixWord ++ tailWord_198387) baseStart_198387 baseEnd_198387 := by
    simpa [prefixWord, tailWord_198387, baseEnd_198387] using wordTrace_append hprefix tailTrace_198387
  have hstable : (prefixWord ++ tailWord_198387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198387).length < 2 ^ (prefixWord ++ tailWord_198387).sum := by decide
  have hdescent : baseEnd_198387 < baseStart_198387 := by decide
  rcases family_descends (prefixWord ++ tailWord_198387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198390 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_198390 : Nat := 118140960795 + 198390 * 2 ^ 59
def prefixEnd_198390 : Nat := 4983230072969 + 3 ^ 40 * 198390 * 2
def baseEnd_198390 : Nat := 101869427045584031912627

theorem tailTrace_198390 : CollatzResearch.WordTrace tailWord_198390 prefixEnd_198390 101869427045584031912627 := by
  unfold tailWord_198390
  simp only [CollatzResearch.WordTrace]
  refine ⟨452242359454649197475039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4823918500849591439733749 452242359454649197475039)
  ·
    refine ⟨678363539181973796212559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 452242359454649197475039 678363539181973796212559)
    ·
      refine ⟨1017545308772960694318839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 678363539181973796212559 1017545308772960694318839)
      ·
        refine ⟨1526317963159441041478259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017545308772960694318839 1526317963159441041478259)
        ·
          refine ⟨2289476944739161562217389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526317963159441041478259 2289476944739161562217389)
          ·
            refine ⟨858553854277185585831521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2289476944739161562217389 858553854277185585831521)
            ·
              refine ⟨643915390707889189373641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858553854277185585831521 643915390707889189373641)
              ·
                refine ⟨482936543030916892030231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643915390707889189373641 482936543030916892030231)
                ·
                  refine ⟨724404814546375338045347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482936543030916892030231 724404814546375338045347)
                  ·
                    refine ⟨1086607221819563007068021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 724404814546375338045347 1086607221819563007068021)
                    ·
                      refine ⟨101869427045584031912627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1086607221819563007068021 101869427045584031912627)
                      ·
                        rfl

theorem cell23_198390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_198390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198390 prefixEnd_198390 := by exact prefixLift 198390
  have htrace : WordTrace (prefixWord ++ tailWord_198390) baseStart_198390 baseEnd_198390 := by
    simpa [prefixWord, tailWord_198390, baseEnd_198390] using wordTrace_append hprefix tailTrace_198390
  have hstable : (prefixWord ++ tailWord_198390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198390).length < 2 ^ (prefixWord ++ tailWord_198390).sum := by decide
  have hdescent : baseEnd_198390 < baseStart_198390 := by decide
  rcases family_descends (prefixWord ++ tailWord_198390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198407 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_198407 : Nat := 118140960795 + 198407 * 2 ^ 59
def prefixEnd_198407 : Nat := 4983230072969 + 3 ^ 40 * 198407 * 2
def baseEnd_198407 : Nat := 101878156216710465400049

theorem tailTrace_198407 : CollatzResearch.WordTrace tailWord_198407 prefixEnd_198407 101878156216710465400049 := by
  unfold tailWord_198407
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236497792212799062969475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4824331861475199375312983 7236497792212799062969475)
  ·
    refine ⟨10854746688319198594454213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7236497792212799062969475 10854746688319198594454213)
    ·
      refine ⟨2035265004059849736460165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10854746688319198594454213 2035265004059849736460165)
      ·
        refine ⟨381612188261221825586281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2035265004059849736460165 381612188261221825586281)
        ·
          refine ⟨286209141195916369189711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381612188261221825586281 286209141195916369189711)
          ·
            refine ⟨429313711793874553784567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286209141195916369189711 429313711793874553784567)
            ·
              refine ⟨643970567690811830676851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429313711793874553784567 643970567690811830676851)
              ·
                refine ⟨965955851536217746015277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643970567690811830676851 965955851536217746015277)
                ·
                  refine ⟨362233444326081654755729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965955851536217746015277 362233444326081654755729)
                  ·
                    refine ⟨271675083244561241066797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 362233444326081654755729 271675083244561241066797)
                    ·
                      refine ⟨101878156216710465400049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 271675083244561241066797 101878156216710465400049)
                      ·
                        rfl

theorem cell23_198407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_198407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198407 prefixEnd_198407 := by exact prefixLift 198407
  have htrace : WordTrace (prefixWord ++ tailWord_198407) baseStart_198407 baseEnd_198407 := by
    simpa [prefixWord, tailWord_198407, baseEnd_198407] using wordTrace_append hprefix tailTrace_198407
  have hstable : (prefixWord ++ tailWord_198407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198407).length < 2 ^ (prefixWord ++ tailWord_198407).sum := by decide
  have hdescent : baseEnd_198407 < baseStart_198407 := by decide
  rcases family_descends (prefixWord ++ tailWord_198407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198437 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 3]
def baseStart_198437 : Nat := 118140960795 + 198437 * 2 ^ 59
def prefixEnd_198437 : Nat := 4983230072969 + 3 ^ 40 * 198437 * 2
def baseEnd_198437 : Nat := 101893560636345348024911

theorem tailTrace_198437 : CollatzResearch.WordTrace tailWord_198437 prefixEnd_198437 101893560636345348024911 := by
  unfold tailWord_198437
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237591982104114186561565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4825061321402742791041043 7237591982104114186561565)
  ·
    refine ⟨2714096993289042819960587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7237591982104114186561565 2714096993289042819960587)
    ·
      refine ⟨4071145489933564229940881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2714096993289042819960587 4071145489933564229940881)
      ·
        refine ⟨3053359117450173172455661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4071145489933564229940881 3053359117450173172455661)
        ·
          refine ⟨1145009669043814939670873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3053359117450173172455661 1145009669043814939670873)
          ·
            refine ⟨858757251782861204753155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145009669043814939670873 858757251782861204753155)
            ·
              refine ⟨1288135877674291807129733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858757251782861204753155 1288135877674291807129733)
              ·
                refine ⟨241525477063929713836825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1288135877674291807129733 241525477063929713836825)
                ·
                  refine ⟨181144107797947285377619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241525477063929713836825 181144107797947285377619)
                  ·
                    refine ⟨271716161696920928066429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181144107797947285377619 271716161696920928066429)
                    ·
                      refine ⟨101893560636345348024911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 271716161696920928066429 101893560636345348024911)
                      ·
                        rfl

theorem cell23_198437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_198437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198437 prefixEnd_198437 := by exact prefixLift 198437
  have htrace : WordTrace (prefixWord ++ tailWord_198437) baseStart_198437 baseEnd_198437 := by
    simpa [prefixWord, tailWord_198437, baseEnd_198437] using wordTrace_append hprefix tailTrace_198437
  have hstable : (prefixWord ++ tailWord_198437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198437).length < 2 ^ (prefixWord ++ tailWord_198437).sum := by decide
  have hdescent : baseEnd_198437 < baseStart_198437 := by decide
  rcases family_descends (prefixWord ++ tailWord_198437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198454 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_198454 : Nat := 118140960795 + 198454 * 2 ^ 59
def prefixEnd_198454 : Nat := 4983230072969 + 3 ^ 40 * 198454 * 2
def baseEnd_198454 : Nat := 101902289807471781512333

theorem tailTrace_198454 : CollatzResearch.WordTrace tailWord_198454 prefixEnd_198454 101902289807471781512333 := by
  unfold tailWord_198454
  simp only [CollatzResearch.WordTrace]
  refine ⟨452388251440157880620651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4825474682028350726620277 452388251440157880620651)
  ·
    refine ⟨678582377160236820930977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 452388251440157880620651 678582377160236820930977)
    ·
      refine ⟨508936782870177615698233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678582377160236820930977 508936782870177615698233)
      ·
        refine ⟨381702587152633211773675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508936782870177615698233 381702587152633211773675)
        ·
          refine ⟨572553880728949817660513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381702587152633211773675 572553880728949817660513)
          ·
            refine ⟨429415410546712363245385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572553880728949817660513 429415410546712363245385)
            ·
              refine ⟨322061557910034272434039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429415410546712363245385 322061557910034272434039)
              ·
                refine ⟨483092336865051408651059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322061557910034272434039 483092336865051408651059)
                ·
                  refine ⟨724638505297577112976589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483092336865051408651059 724638505297577112976589)
                  ·
                    refine ⟨271739439486591417366221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 724638505297577112976589 271739439486591417366221)
                    ·
                      refine ⟨101902289807471781512333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 271739439486591417366221 101902289807471781512333)
                      ·
                        rfl

theorem cell23_198454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_198454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198454 prefixEnd_198454 := by exact prefixLift 198454
  have htrace : WordTrace (prefixWord ++ tailWord_198454) baseStart_198454 baseEnd_198454 := by
    simpa [prefixWord, tailWord_198454, baseEnd_198454] using wordTrace_append hprefix tailTrace_198454
  have hstable : (prefixWord ++ tailWord_198454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198454).length < 2 ^ (prefixWord ++ tailWord_198454).sum := by decide
  have hdescent : baseEnd_198454 < baseStart_198454 := by decide
  rcases family_descends (prefixWord ++ tailWord_198454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198473 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_198473 : Nat := 118140960795 + 198473 * 2 ^ 59
def prefixEnd_198473 : Nat := 4983230072969 + 3 ^ 40 * 198473 * 2
def baseEnd_198473 : Nat := 101912045939907207174745

theorem tailTrace_198473 : CollatzResearch.WordTrace tailWord_198473 prefixEnd_198473 101912045939907207174745 := by
  unfold tailWord_198473
  simp only [CollatzResearch.WordTrace]
  refine ⟨7238905009973692334872073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4825936673315794889914715 7238905009973692334872073)
  ·
    refine ⟨5429178757480269251154055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7238905009973692334872073 5429178757480269251154055)
    ·
      refine ⟨8143768136220403876731083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5429178757480269251154055 8143768136220403876731083)
      ·
        refine ⟨12215652204330605815096625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8143768136220403876731083 12215652204330605815096625)
        ·
          refine ⟨9161739153247954361322469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12215652204330605815096625 9161739153247954361322469)
          ·
            refine ⟨1717826091233991442747963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9161739153247954361322469 1717826091233991442747963)
            ·
              refine ⟨2576739136850987164121945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717826091233991442747963 2576739136850987164121945)
              ·
                refine ⟨1932554352638240373091459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576739136850987164121945 1932554352638240373091459)
                ·
                  refine ⟨2898831528957360559637189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932554352638240373091459 2898831528957360559637189)
                  ·
                    refine ⟨543530911679505104931973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2898831528957360559637189 543530911679505104931973)
                    ·
                      refine ⟨101912045939907207174745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 543530911679505104931973 101912045939907207174745)
                      ·
                        rfl

theorem cell23_198473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_198473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198473 prefixEnd_198473 := by exact prefixLift 198473
  have htrace : WordTrace (prefixWord ++ tailWord_198473) baseStart_198473 baseEnd_198473 := by
    simpa [prefixWord, tailWord_198473, baseEnd_198473] using wordTrace_append hprefix tailTrace_198473
  have hstable : (prefixWord ++ tailWord_198473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198473).length < 2 ^ (prefixWord ++ tailWord_198473).sum := by decide
  have hdescent : baseEnd_198473 < baseStart_198473 := by decide
  rcases family_descends (prefixWord ++ tailWord_198473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198481 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 1, 3, 2]
def baseStart_198481 : Nat := 118140960795 + 198481 * 2 ^ 59
def prefixEnd_198481 : Nat := 4983230072969 + 3 ^ 40 * 198481 * 2
def baseEnd_198481 : Nat := 101916153785143175874709

theorem tailTrace_198481 : CollatzResearch.WordTrace tailWord_198481 prefixEnd_198481 101916153785143175874709 := by
  unfold tailWord_198481
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239196793944709701163297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4826131195963139800775531 7239196793944709701163297)
  ·
    refine ⟨5429397595458532275872473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7239196793944709701163297 5429397595458532275872473)
    ·
      refine ⟨4072048196593899206904355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5429397595458532275872473 4072048196593899206904355)
      ·
        refine ⟨6108072294890848810356533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072048196593899206904355 6108072294890848810356533)
        ·
          refine ⟨572631777646017075970925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6108072294890848810356533 572631777646017075970925)
          ·
            refine ⟨214736916617256403489097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 572631777646017075970925 214736916617256403489097)
            ·
              refine ⟨161052687462942302616823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214736916617256403489097 161052687462942302616823)
              ·
                refine ⟨241579031194413453925235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161052687462942302616823 241579031194413453925235)
                ·
                  refine ⟨362368546791620180887853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241579031194413453925235 362368546791620180887853)
                  ·
                    refine ⟨135888205046857567832945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362368546791620180887853 135888205046857567832945)
                    ·
                      refine ⟨101916153785143175874709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135888205046857567832945 101916153785143175874709)
                      ·
                        rfl

theorem cell23_198481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_198481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198481 prefixEnd_198481 := by exact prefixLift 198481
  have htrace : WordTrace (prefixWord ++ tailWord_198481) baseStart_198481 baseEnd_198481 := by
    simpa [prefixWord, tailWord_198481, baseEnd_198481] using wordTrace_append hprefix tailTrace_198481
  have hstable : (prefixWord ++ tailWord_198481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198481).length < 2 ^ (prefixWord ++ tailWord_198481).sum := by decide
  have hdescent : baseEnd_198481 < baseStart_198481 := by decide
  rcases family_descends (prefixWord ++ tailWord_198481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198513 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 3, 7]
def baseStart_198513 : Nat := 118140960795 + 198513 * 2 ^ 59
def prefixEnd_198513 : Nat := 4983230072969 + 3 ^ 40 * 198513 * 2
def baseEnd_198513 : Nat := 33977528388695683558187

theorem tailTrace_198513 : CollatzResearch.WordTrace tailWord_198513 prefixEnd_198513 33977528388695683558187 := by
  unfold tailWord_198513
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240363929828779166328193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4826909286552519444218795 7240363929828779166328193)
  ·
    refine ⟨5430272947371584374746145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7240363929828779166328193 5430272947371584374746145)
    ·
      refine ⟨4072704710528688281059609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5430272947371584374746145 4072704710528688281059609)
      ·
        refine ⟨3054528532896516210794707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4072704710528688281059609 3054528532896516210794707)
        ·
          refine ⟨4581792799344774316192061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054528532896516210794707 4581792799344774316192061)
          ·
            refine ⟨1718172299754290368572023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4581792799344774316192061 1718172299754290368572023)
            ·
              refine ⟨2577258449631435552858035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718172299754290368572023 2577258449631435552858035)
              ·
                refine ⟨3865887674447153329287053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577258449631435552858035 3865887674447153329287053)
                ·
                  refine ⟨1449707877917682498482645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3865887674447153329287053 1449707877917682498482645)
                  ·
                    refine ⟨33977528388695683558187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1449707877917682498482645 33977528388695683558187)
                    ·
                      rfl

theorem cell23_198513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_198513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198513 prefixEnd_198513 := by exact prefixLift 198513
  have htrace : WordTrace (prefixWord ++ tailWord_198513) baseStart_198513 baseEnd_198513 := by
    simpa [prefixWord, tailWord_198513, baseEnd_198513] using wordTrace_append hprefix tailTrace_198513
  have hstable : (prefixWord ++ tailWord_198513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198513).length < 2 ^ (prefixWord ++ tailWord_198513).sum := by decide
  have hdescent : baseEnd_198513 < baseStart_198513 := by decide
  rcases family_descends (prefixWord ++ tailWord_198513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198520 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 3, 7, 2]
def baseStart_198520 : Nat := 118140960795 + 198520 * 2 ^ 59
def prefixEnd_198520 : Nat := 4983230072969 + 3 ^ 40 * 198520 * 2
def baseEnd_198520 : Nat := 101936179530668523287029

theorem tailTrace_198520 : CollatzResearch.WordTrace tailWord_198520 prefixEnd_198520 101936179530668523287029 := by
  unfold tailWord_198520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3620309620401709680916507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4827079493868946241222009 3620309620401709680916507)
  ·
    refine ⟨5430464430602564521374761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3620309620401709680916507 5430464430602564521374761)
    ·
      refine ⟨4072848322951923391031071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5430464430602564521374761 4072848322951923391031071)
      ·
        refine ⟨6109272484427885086546607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072848322951923391031071 6109272484427885086546607)
        ·
          refine ⟨9163908726641827629819911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6109272484427885086546607 9163908726641827629819911)
          ·
            refine ⟨13745863089962741444729867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9163908726641827629819911 13745863089962741444729867)
            ·
              refine ⟨20618794634944112167094801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13745863089962741444729867 20618794634944112167094801)
              ·
                refine ⟨15464095976208084125321101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20618794634944112167094801 15464095976208084125321101)
                ·
                  refine ⟨5799035991078031546995413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15464095976208084125321101 5799035991078031546995413)
                  ·
                    refine ⟨135914906040891364382705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5799035991078031546995413 135914906040891364382705)
                    ·
                      refine ⟨101936179530668523287029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 135914906040891364382705 101936179530668523287029)
                      ·
                        rfl

theorem cell23_198520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_198520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198520 prefixEnd_198520 := by exact prefixLift 198520
  have htrace : WordTrace (prefixWord ++ tailWord_198520) baseStart_198520 baseEnd_198520 := by
    simpa [prefixWord, tailWord_198520, baseEnd_198520] using wordTrace_append hprefix tailTrace_198520
  have hstable : (prefixWord ++ tailWord_198520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198520).length < 2 ^ (prefixWord ++ tailWord_198520).sum := by decide
  have hdescent : baseEnd_198520 < baseStart_198520 := by decide
  rcases family_descends (prefixWord ++ tailWord_198520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198523 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 5]
def baseStart_198523 : Nat := 118140960795 + 198523 * 2 ^ 59
def prefixEnd_198523 : Nat := 4983230072969 + 3 ^ 40 * 198523 * 2
def baseEnd_198523 : Nat := 101937719972632011549515

theorem tailTrace_198523 : CollatzResearch.WordTrace tailWord_198523 prefixEnd_198523 101937719972632011549515 := by
  unfold tailWord_198523
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240728659792550874192223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4827152439861700582794815 7240728659792550874192223)
  ·
    refine ⟨10861092989688826311288335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7240728659792550874192223 10861092989688826311288335)
    ·
      refine ⟨16291639484533239466932503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10861092989688826311288335 16291639484533239466932503)
      ·
        refine ⟨24437459226799859200398755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16291639484533239466932503 24437459226799859200398755)
        ·
          refine ⟨36656188840199788800598133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24437459226799859200398755 36656188840199788800598133)
          ·
            refine ⟨3436517703768730200056075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36656188840199788800598133 3436517703768730200056075)
            ·
              refine ⟨5154776555653095300084113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436517703768730200056075 5154776555653095300084113)
              ·
                refine ⟨3866082416739821475063085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5154776555653095300084113 3866082416739821475063085)
                ·
                  refine ⟨1449780906277433053148657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3866082416739821475063085 1449780906277433053148657)
                  ·
                    refine ⟨1087335679708074789861493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1449780906277433053148657 1087335679708074789861493)
                    ·
                      refine ⟨101937719972632011549515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1087335679708074789861493 101937719972632011549515)
                      ·
                        rfl

theorem cell23_198523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_198523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198523 prefixEnd_198523 := by exact prefixLift 198523
  have htrace : WordTrace (prefixWord ++ tailWord_198523) baseStart_198523 baseEnd_198523 := by
    simpa [prefixWord, tailWord_198523, baseEnd_198523] using wordTrace_append hprefix tailTrace_198523
  have hstable : (prefixWord ++ tailWord_198523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198523).length < 2 ^ (prefixWord ++ tailWord_198523).sum := by decide
  have hdescent : baseEnd_198523 < baseStart_198523 := by decide
  rcases family_descends (prefixWord ++ tailWord_198523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198634 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_198634 : Nat := 118140960795 + 198634 * 2 ^ 59
def prefixEnd_198634 : Nat := 4983230072969 + 3 ^ 40 * 198634 * 2
def baseEnd_198634 : Nat := 101994716325281077261505

theorem tailTrace_198634 : CollatzResearch.WordTrace tailWord_198634 prefixEnd_198634 101994716325281077261505 := by
  unfold tailWord_198634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811194290597604207870739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4829851441593611220988637 1811194290597604207870739)
  ·
    refine ⟨2716791435896406311806109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1811194290597604207870739 2716791435896406311806109)
    ·
      refine ⟨1018796788461152366927291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2716791435896406311806109 1018796788461152366927291)
      ·
        refine ⟨1528195182691728550390937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018796788461152366927291 1528195182691728550390937)
        ·
          refine ⟨1146146387018796412793203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528195182691728550390937 1146146387018796412793203)
          ·
            refine ⟨1719219580528194619189805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146146387018796412793203 1719219580528194619189805)
            ·
              refine ⟨644707342698072982196177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1719219580528194619189805 644707342698072982196177)
              ·
                refine ⟨483530507023554736647133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644707342698072982196177 483530507023554736647133)
                ·
                  refine ⟨181323940133833026242675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483530507023554736647133 181323940133833026242675)
                  ·
                    refine ⟨271985910200749539364013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181323940133833026242675 271985910200749539364013)
                    ·
                      refine ⟨101994716325281077261505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 271985910200749539364013 101994716325281077261505)
                      ·
                        rfl

theorem cell23_198634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_198634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198634 prefixEnd_198634 := by exact prefixLift 198634
  have htrace : WordTrace (prefixWord ++ tailWord_198634) baseStart_198634 baseEnd_198634 := by
    simpa [prefixWord, tailWord_198634, baseEnd_198634] using wordTrace_append hprefix tailTrace_198634
  have hstable : (prefixWord ++ tailWord_198634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198634).length < 2 ^ (prefixWord ++ tailWord_198634).sum := by decide
  have hdescent : baseEnd_198634 < baseStart_198634 := by decide
  rcases family_descends (prefixWord ++ tailWord_198634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198667 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 4, 4]
def baseStart_198667 : Nat := 118140960795 + 198667 * 2 ^ 59
def prefixEnd_198667 : Nat := 4983230072969 + 3 ^ 40 * 198667 * 2
def baseEnd_198667 : Nat := 34003887062293149382951

theorem tailTrace_198667 : CollatzResearch.WordTrace tailWord_198667 prefixEnd_198667 34003887062293149382951 := by
  unfold tailWord_198667
  simp only [CollatzResearch.WordTrace]
  refine ⟨7245980771270863467434255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4830653847513908978289503 7245980771270863467434255)
  ·
    refine ⟨10868971156906295201151383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7245980771270863467434255 10868971156906295201151383)
    ·
      refine ⟨16303456735359442801727075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10868971156906295201151383 16303456735359442801727075)
      ·
        refine ⟨24455185103039164202590613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16303456735359442801727075 24455185103039164202590613)
        ·
          refine ⟨1146336801704960821996435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24455185103039164202590613 1146336801704960821996435)
          ·
            refine ⟨1719505202557441232994653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146336801704960821996435 1719505202557441232994653)
            ·
              refine ⟨644814450959040462372995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1719505202557441232994653 644814450959040462372995)
              ·
                refine ⟨967221676438560693559493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644814450959040462372995 967221676438560693559493)
                ·
                  refine ⟨181354064332230130042405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 967221676438560693559493 181354064332230130042405)
                  ·
                    refine ⟨34003887062293149382951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181354064332230130042405 34003887062293149382951)
                    ·
                      rfl

theorem cell23_198667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 4].length) (baseStart_198667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198667 prefixEnd_198667 := by exact prefixLift 198667
  have htrace : WordTrace (prefixWord ++ tailWord_198667) baseStart_198667 baseEnd_198667 := by
    simpa [prefixWord, tailWord_198667, baseEnd_198667] using wordTrace_append hprefix tailTrace_198667
  have hstable : (prefixWord ++ tailWord_198667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198667).length < 2 ^ (prefixWord ++ tailWord_198667).sum := by decide
  have hdescent : baseEnd_198667 < baseStart_198667 := by decide
  rcases family_descends (prefixWord ++ tailWord_198667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198680 : List Nat := [2, 1, 2, 3, 2, 1, 2, 10]
def baseStart_198680 : Nat := 118140960795 + 198680 * 2 ^ 59
def prefixEnd_198680 : Nat := 4983230072969 + 3 ^ 40 * 198680 * 2
def baseEnd_198680 : Nat := 3778456905014366566159

theorem tailTrace_198680 : CollatzResearch.WordTrace tailWord_198680 prefixEnd_198680 3778456905014366566159 := by
  unfold tailWord_198680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623227460111883343828747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4830969946815844458438329 3623227460111883343828747)
  ·
    refine ⟨5434841190167825015743121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3623227460111883343828747 5434841190167825015743121)
    ·
      refine ⟨4076130892625868761807341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5434841190167825015743121 4076130892625868761807341)
      ·
        refine ⟨1528549084734700785677753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4076130892625868761807341 1528549084734700785677753)
        ·
          refine ⟨1146411813551025589258315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528549084734700785677753 1146411813551025589258315)
          ·
            refine ⟨1719617720326538383887473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146411813551025589258315 1719617720326538383887473)
            ·
              refine ⟨1289713290244903787915605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719617720326538383887473 1289713290244903787915605)
              ·
                refine ⟨3778456905014366566159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1289713290244903787915605 3778456905014366566159)
                ·
                  rfl

theorem cell23_198680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 10].length) (baseStart_198680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198680 prefixEnd_198680 := by exact prefixLift 198680
  have htrace : WordTrace (prefixWord ++ tailWord_198680) baseStart_198680 baseEnd_198680 := by
    simpa [prefixWord, tailWord_198680, baseEnd_198680] using wordTrace_append hprefix tailTrace_198680
  have hstable : (prefixWord ++ tailWord_198680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198680).length < 2 ^ (prefixWord ++ tailWord_198680).sum := by decide
  have hdescent : baseEnd_198680 < baseStart_198680 := by decide
  rcases family_descends (prefixWord ++ tailWord_198680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198684 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_198684 : Nat := 118140960795 + 198684 * 2 ^ 59
def prefixEnd_198684 : Nat := 4983230072969 + 3 ^ 40 * 198684 * 2
def baseEnd_198684 : Nat := 34006796786001960545425

theorem tailTrace_198684 : CollatzResearch.WordTrace tailWord_198684 prefixEnd_198684 34006796786001960545425 := by
  unfold tailWord_198684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623300406104637685401553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4831067208139516913868737 3623300406104637685401553)
  ·
    refine ⟨2717475304578478264051165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3623300406104637685401553 2717475304578478264051165)
    ·
      refine ⟨1019053239216929349019187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2717475304578478264051165 1019053239216929349019187)
      ·
        refine ⟨1528579858825394023528781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019053239216929349019187 1528579858825394023528781)
        ·
          refine ⟨573217447059522758823293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1528579858825394023528781 573217447059522758823293)
          ·
            refine ⟨214956542647321034558735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 573217447059522758823293 214956542647321034558735)
            ·
              refine ⟨322434813970981551838103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214956542647321034558735 322434813970981551838103)
              ·
                refine ⟨483652220956472327757155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322434813970981551838103 483652220956472327757155)
                ·
                  refine ⟨725478331434708491635733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483652220956472327757155 725478331434708491635733)
                  ·
                    refine ⟨34006796786001960545425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 725478331434708491635733 34006796786001960545425)
                    ·
                      rfl

theorem cell23_198684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_198684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198684 prefixEnd_198684 := by exact prefixLift 198684
  have htrace : WordTrace (prefixWord ++ tailWord_198684) baseStart_198684 baseEnd_198684 := by
    simpa [prefixWord, tailWord_198684, baseEnd_198684] using wordTrace_append hprefix tailTrace_198684
  have hstable : (prefixWord ++ tailWord_198684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198684).length < 2 ^ (prefixWord ++ tailWord_198684).sum := by decide
  have hdescent : baseEnd_198684 < baseStart_198684 := by decide
  rcases family_descends (prefixWord ++ tailWord_198684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198707 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 3]
def baseStart_198707 : Nat := 118140960795 + 198707 * 2 ^ 59
def prefixEnd_198707 : Nat := 4983230072969 + 3 ^ 40 * 198707 * 2
def baseEnd_198707 : Nat := 102032200413059291648669

theorem tailTrace_198707 : CollatzResearch.WordTrace tailWord_198707 prefixEnd_198707 102032200413059291648669 := by
  unfold tailWord_198707
  simp only [CollatzResearch.WordTrace]
  refine ⟨7247439691125950298890375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4831626460750633532593583 7247439691125950298890375)
  ·
    refine ⟨10871159536688925448335563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7247439691125950298890375 10871159536688925448335563)
    ·
      refine ⟨16306739305033388172503345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10871159536688925448335563 16306739305033388172503345)
      ·
        refine ⟨12230054478775041129377509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16306739305033388172503345 12230054478775041129377509)
        ·
          refine ⟨2293135214770320211758283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12230054478775041129377509 2293135214770320211758283)
          ·
            refine ⟨3439702822155480317637425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293135214770320211758283 3439702822155480317637425)
            ·
              refine ⟨2579777116616610238228069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3439702822155480317637425 2579777116616610238228069)
              ·
                refine ⟨483708209365614419667763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2579777116616610238228069 483708209365614419667763)
                ·
                  refine ⟨725562314048421629501645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483708209365614419667763 725562314048421629501645)
                  ·
                    refine ⟨272085867768158111063117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 725562314048421629501645 272085867768158111063117)
                    ·
                      refine ⟨102032200413059291648669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 272085867768158111063117 102032200413059291648669)
                      ·
                        rfl

theorem cell23_198707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_198707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198707 prefixEnd_198707 := by exact prefixLift 198707
  have htrace : WordTrace (prefixWord ++ tailWord_198707) baseStart_198707 baseEnd_198707 := by
    simpa [prefixWord, tailWord_198707, baseEnd_198707] using wordTrace_append hprefix tailTrace_198707
  have hstable : (prefixWord ++ tailWord_198707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198707).length < 2 ^ (prefixWord ++ tailWord_198707).sum := by decide
  have hdescent : baseEnd_198707 < baseStart_198707 := by decide
  rcases family_descends (prefixWord ++ tailWord_198707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198741 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_198741 : Nat := 118140960795 + 198741 * 2 ^ 59
def prefixEnd_198741 : Nat := 4983230072969 + 3 ^ 40 * 198741 * 2
def baseEnd_198741 : Nat := 102049658755312158623513

theorem tailTrace_198741 : CollatzResearch.WordTrace tailWord_198741 prefixEnd_198741 102049658755312158623513 := by
  unfold tailWord_198741
  simp only [CollatzResearch.WordTrace]
  refine ⟨7248679773002774105628077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4832453182001849403752051 7248679773002774105628077)
  ·
    refine ⟨2718254914876040289610529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7248679773002774105628077 2718254914876040289610529)
    ·
      refine ⟨2038691186157030217207897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2718254914876040289610529 2038691186157030217207897)
      ·
        refine ⟨1529018389617772662905923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2038691186157030217207897 1529018389617772662905923)
        ·
          refine ⟨2293527584426658994358885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529018389617772662905923 2293527584426658994358885)
          ·
            refine ⟨430036422079998561442291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2293527584426658994358885 430036422079998561442291)
            ·
              refine ⟨645054633119997842163437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430036422079998561442291 645054633119997842163437)
              ·
                refine ⟨241895487419999190811289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 645054633119997842163437 241895487419999190811289)
                ·
                  refine ⟨181421615564999393108467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241895487419999190811289 181421615564999393108467)
                  ·
                    refine ⟨272132423347499089662701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181421615564999393108467 272132423347499089662701)
                    ·
                      refine ⟨102049658755312158623513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 272132423347499089662701 102049658755312158623513)
                      ·
                        rfl

theorem cell23_198741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_198741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198741 prefixEnd_198741 := by exact prefixLift 198741
  have htrace : WordTrace (prefixWord ++ tailWord_198741) baseStart_198741 baseEnd_198741 := by
    simpa [prefixWord, tailWord_198741, baseEnd_198741] using wordTrace_append hprefix tailTrace_198741
  have hstable : (prefixWord ++ tailWord_198741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198741).length < 2 ^ (prefixWord ++ tailWord_198741).sum := by decide
  have hdescent : baseEnd_198741 < baseStart_198741 := by decide
  rcases family_descends (prefixWord ++ tailWord_198741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198764 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 3, 4, 2]
def baseStart_198764 : Nat := 118140960795 + 198764 * 2 ^ 59
def prefixEnd_198764 : Nat := 4983230072969 + 3 ^ 40 * 198764 * 2
def baseEnd_198764 : Nat := 102061468810365568635907

theorem tailTrace_198764 : CollatzResearch.WordTrace tailWord_198764 prefixEnd_198764 102061468810365568635907 := by
  unfold tailWord_198764
  simp only [CollatzResearch.WordTrace]
  refine ⟨3624759325959724516857673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4833012434612966022476897 3624759325959724516857673)
  ·
    refine ⟨2718569494469793387643255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3624759325959724516857673 2718569494469793387643255)
    ·
      refine ⟨4077854241704690081464883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2718569494469793387643255 4077854241704690081464883)
      ·
        refine ⟨6116781362557035122197325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4077854241704690081464883 6116781362557035122197325)
        ·
          refine ⟨2293793010958888170823997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6116781362557035122197325 2293793010958888170823997)
          ·
            refine ⟨860172379109583064058999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2293793010958888170823997 860172379109583064058999)
            ·
              refine ⟨1290258568664374596088499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860172379109583064058999 1290258568664374596088499)
              ·
                refine ⟨1935387852996561894132749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290258568664374596088499 1935387852996561894132749)
                ·
                  refine ⟨725770444873710710299781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1935387852996561894132749 725770444873710710299781)
                  ·
                    refine ⟨136081958413820758181209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 725770444873710710299781 136081958413820758181209)
                    ·
                      refine ⟨102061468810365568635907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136081958413820758181209 102061468810365568635907)
                      ·
                        rfl

theorem cell23_198764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_198764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198764 prefixEnd_198764 := by exact prefixLift 198764
  have htrace : WordTrace (prefixWord ++ tailWord_198764) baseStart_198764 baseEnd_198764 := by
    simpa [prefixWord, tailWord_198764, baseEnd_198764] using wordTrace_append hprefix tailTrace_198764
  have hstable : (prefixWord ++ tailWord_198764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198764).length < 2 ^ (prefixWord ++ tailWord_198764).sum := by decide
  have hdescent : baseEnd_198764 < baseStart_198764 := by decide
  rcases family_descends (prefixWord ++ tailWord_198764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198767 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_198767 : Nat := 118140960795 + 198767 * 2 ^ 59
def prefixEnd_198767 : Nat := 4983230072969 + 3 ^ 40 * 198767 * 2
def baseEnd_198767 : Nat := 102063009252329056898393

theorem tailTrace_198767 : CollatzResearch.WordTrace tailWord_198767 prefixEnd_198767 102063009252329056898393 := by
  unfold tailWord_198767
  simp only [CollatzResearch.WordTrace]
  refine ⟨7249628070908580546074555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4833085380605720364049703 7249628070908580546074555)
  ·
    refine ⟨10874442106362870819111833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7249628070908580546074555 10874442106362870819111833)
    ·
      refine ⟨8155831579772153114333875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10874442106362870819111833 8155831579772153114333875)
      ·
        refine ⟨12233747369658229671500813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8155831579772153114333875 12233747369658229671500813)
        ·
          refine ⟨4587655263621836126812805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12233747369658229671500813 4587655263621836126812805)
          ·
            refine ⟨860185361929094273777401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4587655263621836126812805 860185361929094273777401)
            ·
              refine ⟨645139021446820705333051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860185361929094273777401 645139021446820705333051)
              ·
                refine ⟨967708532170231057999577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645139021446820705333051 967708532170231057999577)
                ·
                  refine ⟨725781399127673293499683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 967708532170231057999577 725781399127673293499683)
                  ·
                    refine ⟨1088672098691509940249525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 725781399127673293499683 1088672098691509940249525)
                    ·
                      refine ⟨102063009252329056898393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1088672098691509940249525 102063009252329056898393)
                      ·
                        rfl

theorem cell23_198767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_198767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198767 prefixEnd_198767 := by exact prefixLift 198767
  have htrace : WordTrace (prefixWord ++ tailWord_198767) baseStart_198767 baseEnd_198767 := by
    simpa [prefixWord, tailWord_198767, baseEnd_198767] using wordTrace_append hprefix tailTrace_198767
  have hstable : (prefixWord ++ tailWord_198767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198767).length < 2 ^ (prefixWord ++ tailWord_198767).sum := by decide
  have hdescent : baseEnd_198767 < baseStart_198767 := by decide
  rcases family_descends (prefixWord ++ tailWord_198767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198768 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 1, 3, 2]
def baseStart_198768 : Nat := 118140960795 + 198768 * 2 ^ 59
def prefixEnd_198768 : Nat := 4983230072969 + 3 ^ 40 * 198768 * 2
def baseEnd_198768 : Nat := 102063522732983552985889

theorem tailTrace_198768 : CollatzResearch.WordTrace tailWord_198768 prefixEnd_198768 102063522732983552985889 := by
  unfold tailWord_198768
  simp only [CollatzResearch.WordTrace]
  refine ⟨3624832271952478858430479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4833109695936638477907305 3624832271952478858430479)
  ·
    refine ⟨5437248407928718287645719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3624832271952478858430479 5437248407928718287645719)
    ·
      refine ⟨8155872611893077431468579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5437248407928718287645719 8155872611893077431468579)
      ·
        refine ⟨12233808917839616147202869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8155872611893077431468579 12233808917839616147202869)
        ·
          refine ⟨1146919586047464013800269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12233808917839616147202869 1146919586047464013800269)
          ·
            refine ⟨430094844767799005175101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1146919586047464013800269 430094844767799005175101)
            ·
              refine ⟨161285566787924626940663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 430094844767799005175101 161285566787924626940663)
              ·
                refine ⟨241928350181886940410995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161285566787924626940663 241928350181886940410995)
                ·
                  refine ⟨362892525272830410616493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241928350181886940410995 362892525272830410616493)
                  ·
                    refine ⟨136084696977311403981185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362892525272830410616493 136084696977311403981185)
                    ·
                      refine ⟨102063522732983552985889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136084696977311403981185 102063522732983552985889)
                      ·
                        rfl

theorem cell23_198768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 3, 2].length) (baseStart_198768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198768 prefixEnd_198768 := by exact prefixLift 198768
  have htrace : WordTrace (prefixWord ++ tailWord_198768) baseStart_198768 baseEnd_198768 := by
    simpa [prefixWord, tailWord_198768, baseEnd_198768] using wordTrace_append hprefix tailTrace_198768
  have hstable : (prefixWord ++ tailWord_198768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198768).length < 2 ^ (prefixWord ++ tailWord_198768).sum := by decide
  have hdescent : baseEnd_198768 < baseStart_198768 := by decide
  rcases family_descends (prefixWord ++ tailWord_198768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198794 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_198794 : Nat := 118140960795 + 198794 * 2 ^ 59
def prefixEnd_198794 : Nat := 4983230072969 + 3 ^ 40 * 198794 * 2
def baseEnd_198794 : Nat := 102076873230000451260769

theorem tailTrace_198794 : CollatzResearch.WordTrace tailWord_198794 prefixEnd_198794 102076873230000451260769 := by
  unfold tailWord_198794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812653210452691039326859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4833741894540509438204957 1812653210452691039326859)
  ·
    refine ⟨2718979815679036558990289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1812653210452691039326859 2718979815679036558990289)
    ·
      refine ⟨2039234861759277419242717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2718979815679036558990289 2039234861759277419242717)
      ·
        refine ⟨764713073159729032216019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2039234861759277419242717 764713073159729032216019)
        ·
          refine ⟨1147069609739593548324029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764713073159729032216019 1147069609739593548324029)
          ·
            refine ⟨430151103652347580621511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1147069609739593548324029 430151103652347580621511)
            ·
              refine ⟨645226655478521370932267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430151103652347580621511 645226655478521370932267)
              ·
                refine ⟨967839983217782056398401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645226655478521370932267 967839983217782056398401)
                ·
                  refine ⟨725879987413336542298801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 967839983217782056398401 725879987413336542298801)
                  ·
                    refine ⟨544409990560002406724101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 725879987413336542298801 544409990560002406724101)
                    ·
                      refine ⟨102076873230000451260769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 544409990560002406724101 102076873230000451260769)
                      ·
                        rfl

theorem cell23_198794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_198794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198794 prefixEnd_198794 := by exact prefixLift 198794
  have htrace : WordTrace (prefixWord ++ tailWord_198794) baseStart_198794 baseEnd_198794 := by
    simpa [prefixWord, tailWord_198794, baseEnd_198794] using wordTrace_append hprefix tailTrace_198794
  have hstable : (prefixWord ++ tailWord_198794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198794).length < 2 ^ (prefixWord ++ tailWord_198794).sum := by decide
  have hdescent : baseEnd_198794 < baseStart_198794 := by decide
  rcases family_descends (prefixWord ++ tailWord_198794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198798 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_198798 : Nat := 118140960795 + 198798 * 2 ^ 59
def prefixEnd_198798 : Nat := 4983230072969 + 3 ^ 40 * 198798 * 2
def baseEnd_198798 : Nat := 102078927152618435610751

theorem tailTrace_198798 : CollatzResearch.WordTrace tailWord_198798 prefixEnd_198798 102078927152618435610751 := by
  unfold tailWord_198798
  simp only [CollatzResearch.WordTrace]
  refine ⟨906344841724534105056631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4833839155864181893635365 906344841724534105056631)
  ·
    refine ⟨1359517262586801157584947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 906344841724534105056631 1359517262586801157584947)
    ·
      refine ⟨2039275893880201736377421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359517262586801157584947 2039275893880201736377421)
      ·
        refine ⟨764728460205075651141533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2039275893880201736377421 764728460205075651141533)
        ·
          refine ⟨286773172576903369178075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 764728460205075651141533 286773172576903369178075)
          ·
            refine ⟨430159758865355053767113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286773172576903369178075 430159758865355053767113)
            ·
              refine ⟨322619819149016290325335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430159758865355053767113 322619819149016290325335)
              ·
                refine ⟨483929728723524435488003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322619819149016290325335 483929728723524435488003)
                ·
                  refine ⟨725894593085286653232005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483929728723524435488003 725894593085286653232005)
                  ·
                    refine ⟨136105236203491247481001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 725894593085286653232005 136105236203491247481001)
                    ·
                      refine ⟨102078927152618435610751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136105236203491247481001 102078927152618435610751)
                      ·
                        rfl

theorem cell23_198798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_198798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198798 prefixEnd_198798 := by exact prefixLift 198798
  have htrace : WordTrace (prefixWord ++ tailWord_198798) baseStart_198798 baseEnd_198798 := by
    simpa [prefixWord, tailWord_198798, baseEnd_198798] using wordTrace_append hprefix tailTrace_198798
  have hstable : (prefixWord ++ tailWord_198798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198798).length < 2 ^ (prefixWord ++ tailWord_198798).sum := by decide
  have hdescent : baseEnd_198798 < baseStart_198798 := by decide
  rcases family_descends (prefixWord ++ tailWord_198798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198874 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_198874 : Nat := 118140960795 + 198874 * 2 ^ 59
def prefixEnd_198874 : Nat := 4983230072969 + 3 ^ 40 * 198874 * 2
def baseEnd_198874 : Nat := 102117951682360138260401

theorem tailTrace_198874 : CollatzResearch.WordTrace tailWord_198874 prefixEnd_198874 102117951682360138260401 := by
  unfold tailWord_198874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813382670380234455054919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4835687121013958546813117 1813382670380234455054919)
  ·
    refine ⟨2720074005570351682582379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1813382670380234455054919 2720074005570351682582379)
    ·
      refine ⟨4080111008355527523873569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2720074005570351682582379 4080111008355527523873569)
      ·
        refine ⟨3060083256266645642905177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4080111008355527523873569 3060083256266645642905177)
        ·
          refine ⟨2295062442199984232178883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060083256266645642905177 2295062442199984232178883)
          ·
            refine ⟨3442593663299976348268325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295062442199984232178883 3442593663299976348268325)
            ·
              refine ⟨645486311868745565300311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3442593663299976348268325 645486311868745565300311)
              ·
                refine ⟨968229467803118347950467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645486311868745565300311 968229467803118347950467)
                ·
                  refine ⟨1452344201704677521925701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968229467803118347950467 1452344201704677521925701)
                  ·
                    refine ⟨272314537819627035361069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1452344201704677521925701 272314537819627035361069)
                    ·
                      refine ⟨102117951682360138260401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 272314537819627035361069 102117951682360138260401)
                      ·
                        rfl

theorem cell23_198874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_198874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198874 prefixEnd_198874 := by exact prefixLift 198874
  have htrace : WordTrace (prefixWord ++ tailWord_198874) baseStart_198874 baseEnd_198874 := by
    simpa [prefixWord, tailWord_198874, baseEnd_198874] using wordTrace_append hprefix tailTrace_198874
  have hstable : (prefixWord ++ tailWord_198874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198874).length < 2 ^ (prefixWord ++ tailWord_198874).sum := by decide
  have hdescent : baseEnd_198874 < baseStart_198874 := by decide
  rcases family_descends (prefixWord ++ tailWord_198874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198894 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_198894 : Nat := 118140960795 + 198894 * 2 ^ 59
def prefixEnd_198894 : Nat := 4983230072969 + 3 ^ 40 * 198894 * 2
def baseEnd_198894 : Nat := 11347580143938895556701

theorem tailTrace_198894 : CollatzResearch.WordTrace tailWord_198894 prefixEnd_198894 11347580143938895556701 := by
  unfold tailWord_198894
  simp only [CollatzResearch.WordTrace]
  refine ⟨906782517681060154493467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4836173427632320823965157 906782517681060154493467)
  ·
    refine ⟨1360173776521590231740201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 906782517681060154493467 1360173776521590231740201)
    ·
      refine ⟨1020130332391192673805151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1360173776521590231740201 1020130332391192673805151)
      ·
        refine ⟨1530195498586789010707727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020130332391192673805151 1530195498586789010707727)
        ·
          refine ⟨2295293247880183516061591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530195498586789010707727 2295293247880183516061591)
          ·
            refine ⟨3442939871820275274092387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295293247880183516061591 3442939871820275274092387)
            ·
              refine ⟨5164409807730412911138581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442939871820275274092387 5164409807730412911138581)
              ·
                refine ⟨242081709737363105209621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5164409807730412911138581 242081709737363105209621)
                ·
                  refine ⟨11347580143938895556701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 242081709737363105209621 11347580143938895556701)
                  ·
                    rfl

theorem cell23_198894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_198894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198894 prefixEnd_198894 := by exact prefixLift 198894
  have htrace : WordTrace (prefixWord ++ tailWord_198894) baseStart_198894 baseEnd_198894 := by
    simpa [prefixWord, tailWord_198894, baseEnd_198894] using wordTrace_append hprefix tailTrace_198894
  have hstable : (prefixWord ++ tailWord_198894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198894).length < 2 ^ (prefixWord ++ tailWord_198894).sum := by decide
  have hdescent : baseEnd_198894 < baseStart_198894 := by decide
  rcases family_descends (prefixWord ++ tailWord_198894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198897 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_198897 : Nat := 118140960795 + 198897 * 2 ^ 59
def prefixEnd_198897 : Nat := 4983230072969 + 3 ^ 40 * 198897 * 2
def baseEnd_198897 : Nat := 102129761737413548272795

theorem tailTrace_198897 : CollatzResearch.WordTrace tailWord_198897 prefixEnd_198897 102129761737413548272795 := by
  unfold tailWord_198897
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254369560437612748306945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4836246373625075165537963 7254369560437612748306945)
  ·
    refine ⟨5440777170328209561230209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7254369560437612748306945 5440777170328209561230209)
    ·
      refine ⟨4080582877746157170922657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5440777170328209561230209 4080582877746157170922657)
      ·
        refine ⟨3060437158309617878191993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4080582877746157170922657 3060437158309617878191993)
        ·
          refine ⟨2295327868732213408643995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060437158309617878191993 2295327868732213408643995)
          ·
            refine ⟨3442991803098320112965993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295327868732213408643995 3442991803098320112965993)
            ·
              refine ⟨2582243852323740084724495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3442991803098320112965993 2582243852323740084724495)
              ·
                refine ⟨3873365778485610127086743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582243852323740084724495 3873365778485610127086743)
                ·
                  refine ⟨5810048667728415190630115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873365778485610127086743 5810048667728415190630115)
                  ·
                    refine ⟨8715073001592622785945173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5810048667728415190630115 8715073001592622785945173)
                    ·
                      refine ⟨102129761737413548272795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 8715073001592622785945173 102129761737413548272795)
                      ·
                        rfl

theorem cell23_198897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_198897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198897 prefixEnd_198897 := by exact prefixLift 198897
  have htrace : WordTrace (prefixWord ++ tailWord_198897) baseStart_198897 baseEnd_198897 := by
    simpa [prefixWord, tailWord_198897, baseEnd_198897] using wordTrace_append hprefix tailTrace_198897
  have hstable : (prefixWord ++ tailWord_198897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198897).length < 2 ^ (prefixWord ++ tailWord_198897).sum := by decide
  have hdescent : baseEnd_198897 < baseStart_198897 := by decide
  rcases family_descends (prefixWord ++ tailWord_198897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198898 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_198898 : Nat := 118140960795 + 198898 * 2 ^ 59
def prefixEnd_198898 : Nat := 4983230072969 + 3 ^ 40 * 198898 * 2
def baseEnd_198898 : Nat := 34043425072689348120097

theorem tailTrace_198898 : CollatzResearch.WordTrace tailWord_198898 prefixEnd_198898 34043425072689348120097 := by
  unfold tailWord_198898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813601508358497479773337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4836270688955993279395565 1813601508358497479773337)
  ·
    refine ⟨1360201131268873109830003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1813601508358497479773337 1360201131268873109830003)
    ·
      refine ⟨2040301696903309664745005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1360201131268873109830003 2040301696903309664745005)
      ·
        refine ⟨765113136338741124279377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2040301696903309664745005 765113136338741124279377)
        ·
          refine ⟨573834852254055843209533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765113136338741124279377 573834852254055843209533)
          ·
            refine ⟨215188069595270941203575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 573834852254055843209533 215188069595270941203575)
            ·
              refine ⟨322782104392906411805363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215188069595270941203575 322782104392906411805363)
              ·
                refine ⟨484173156589359617708045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322782104392906411805363 484173156589359617708045)
                ·
                  refine ⟨181564933721009856640517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484173156589359617708045 181564933721009856640517)
                  ·
                    refine ⟨34043425072689348120097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181564933721009856640517 34043425072689348120097)
                    ·
                      rfl

theorem cell23_198898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_198898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198898 prefixEnd_198898 := by exact prefixLift 198898
  have htrace : WordTrace (prefixWord ++ tailWord_198898) baseStart_198898 baseEnd_198898 := by
    simpa [prefixWord, tailWord_198898, baseEnd_198898] using wordTrace_append hprefix tailTrace_198898
  have hstable : (prefixWord ++ tailWord_198898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198898).length < 2 ^ (prefixWord ++ tailWord_198898).sum := by decide
  have hdescent : baseEnd_198898 < baseStart_198898 := by decide
  rcases family_descends (prefixWord ++ tailWord_198898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198917 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_198917 : Nat := 118140960795 + 198917 * 2 ^ 59
def prefixEnd_198917 : Nat := 4983230072969 + 3 ^ 40 * 198917 * 2
def baseEnd_198917 : Nat := 102140031350503470022703

theorem tailTrace_198917 : CollatzResearch.WordTrace tailWord_198917 prefixEnd_198917 102140031350503470022703 := by
  unfold tailWord_198917
  simp only [CollatzResearch.WordTrace]
  refine ⟨7255099020365156164035005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4836732680243437442690003 7255099020365156164035005)
  ·
    refine ⟨2720662132636933561513127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7255099020365156164035005 2720662132636933561513127)
    ·
      refine ⟨4080993198955400342269691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2720662132636933561513127 4080993198955400342269691)
      ·
        refine ⟨6121489798433100513404537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4080993198955400342269691 6121489798433100513404537)
        ·
          refine ⟨4591117348824825385053403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6121489798433100513404537 4591117348824825385053403)
          ·
            refine ⟨6886676023237238077580105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591117348824825385053403 6886676023237238077580105)
            ·
              refine ⟨5165007017427928558185079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6886676023237238077580105 5165007017427928558185079)
              ·
                refine ⟨7747510526141892837277619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5165007017427928558185079 7747510526141892837277619)
                ·
                  refine ⟨11621265789212839255916429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7747510526141892837277619 11621265789212839255916429)
                  ·
                    refine ⟨4357974670954814720968661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11621265789212839255916429 4357974670954814720968661)
                    ·
                      refine ⟨102140031350503470022703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4357974670954814720968661 102140031350503470022703)
                      ·
                        rfl

theorem cell23_198917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_198917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198917 prefixEnd_198917 := by exact prefixLift 198917
  have htrace : WordTrace (prefixWord ++ tailWord_198917) baseStart_198917 baseEnd_198917 := by
    simpa [prefixWord, tailWord_198917, baseEnd_198917] using wordTrace_append hprefix tailTrace_198917
  have hstable : (prefixWord ++ tailWord_198917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198917).length < 2 ^ (prefixWord ++ tailWord_198917).sum := by decide
  have hdescent : baseEnd_198917 < baseStart_198917 := by decide
  rcases family_descends (prefixWord ++ tailWord_198917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198924 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_198924 : Nat := 118140960795 + 198924 * 2 ^ 59
def prefixEnd_198924 : Nat := 4983230072969 + 3 ^ 40 * 198924 * 2
def baseEnd_198924 : Nat := 34047875238361647545057

theorem tailTrace_198924 : CollatzResearch.WordTrace tailWord_198924 prefixEnd_198924 34047875238361647545057 := by
  unfold tailWord_198924
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627677165669898179769913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4836902887559864239693217 3627677165669898179769913)
  ·
    refine ⟨2720757874252423634827435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3627677165669898179769913 2720757874252423634827435)
    ·
      refine ⟨4081136811378635452241153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2720757874252423634827435 4081136811378635452241153)
      ·
        refine ⟨3060852608533976589180865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4081136811378635452241153 3060852608533976589180865)
        ·
          refine ⟨2295639456400482441885649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060852608533976589180865 2295639456400482441885649)
          ·
            refine ⟨1721729592300361831414237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2295639456400482441885649 1721729592300361831414237)
            ·
              refine ⟨645648597112635686780339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1721729592300361831414237 645648597112635686780339)
              ·
                refine ⟨968472895668953530170509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645648597112635686780339 968472895668953530170509)
                ·
                  refine ⟨363177335875857573813941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968472895668953530170509 363177335875857573813941)
                  ·
                    refine ⟨34047875238361647545057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 363177335875857573813941 34047875238361647545057)
                    ·
                      rfl

theorem cell23_198924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_198924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198924 prefixEnd_198924 := by exact prefixLift 198924
  have htrace : WordTrace (prefixWord ++ tailWord_198924) baseStart_198924 baseEnd_198924 := by
    simpa [prefixWord, tailWord_198924, baseEnd_198924] using wordTrace_append hprefix tailTrace_198924
  have hstable : (prefixWord ++ tailWord_198924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198924).length < 2 ^ (prefixWord ++ tailWord_198924).sum := by decide
  have hdescent : baseEnd_198924 < baseStart_198924 := by decide
  rcases family_descends (prefixWord ++ tailWord_198924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198948 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_198948 : Nat := 118140960795 + 198948 * 2 ^ 59
def prefixEnd_198948 : Nat := 4983230072969 + 3 ^ 40 * 198948 * 2
def baseEnd_198948 : Nat := 102155949250792848735061

theorem tailTrace_198948 : CollatzResearch.WordTrace tailWord_198948 prefixEnd_198948 102155949250792848735061 := by
  unfold tailWord_198948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3628114841626424229206749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4837486455501898972275665 3628114841626424229206749)
  ·
    refine ⟨1360543065609909085952531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3628114841626424229206749 1360543065609909085952531)
    ·
      refine ⟨2040814598414863628928797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1360543065609909085952531 2040814598414863628928797)
      ·
        refine ⟨765305474405573860848299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2040814598414863628928797 765305474405573860848299)
        ·
          refine ⟨1147958211608360791272449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765305474405573860848299 1147958211608360791272449)
          ·
            refine ⟨860968658706270593454337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1147958211608360791272449 860968658706270593454337)
            ·
              refine ⟨645726494029702945090753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860968658706270593454337 645726494029702945090753)
              ·
                refine ⟨484294870522277208818065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645726494029702945090753 484294870522277208818065)
                ·
                  refine ⟨363221152891707906613549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484294870522277208818065 363221152891707906613549)
                  ·
                    refine ⟨136207932334390464980081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363221152891707906613549 136207932334390464980081)
                    ·
                      refine ⟨102155949250792848735061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136207932334390464980081 102155949250792848735061)
                      ·
                        rfl

theorem cell23_198948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_198948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_198948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_198948 prefixEnd_198948 := by exact prefixLift 198948
  have htrace : WordTrace (prefixWord ++ tailWord_198948) baseStart_198948 baseEnd_198948 := by
    simpa [prefixWord, tailWord_198948, baseEnd_198948] using wordTrace_append hprefix tailTrace_198948
  have hstable : (prefixWord ++ tailWord_198948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198948).length < 2 ^ (prefixWord ++ tailWord_198948).sum := by decide
  have hdescent : baseEnd_198948 < baseStart_198948 := by decide
  rcases family_descends (prefixWord ++ tailWord_198948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199006 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_199006 : Nat := 118140960795 + 199006 * 2 ^ 59
def prefixEnd_199006 : Nat := 4983230072969 + 3 ^ 40 * 199006 * 2
def baseEnd_199006 : Nat := 102185731128753621809795

theorem tailTrace_199006 : CollatzResearch.WordTrace tailWord_199006 prefixEnd_199006 102185731128753621809795 := by
  unfold tailWord_199006
  simp only [CollatzResearch.WordTrace]
  refine ⟨907293139630340545503109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4838896744695149576016581 907293139630340545503109)
  ·
    refine ⟨170117463680688852281833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 907293139630340545503109 170117463680688852281833)
    ·
      refine ⟨127588097760516639211375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170117463680688852281833 127588097760516639211375)
      ·
        refine ⟨191382146640774958817063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127588097760516639211375 191382146640774958817063)
        ·
          refine ⟨287073219961162438225595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191382146640774958817063 287073219961162438225595)
          ·
            refine ⟨430609829941743657338393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287073219961162438225595 430609829941743657338393)
            ·
              refine ⟨322957372456307743003795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430609829941743657338393 322957372456307743003795)
              ·
                refine ⟨484436058684461614505693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322957372456307743003795 484436058684461614505693)
                ·
                  refine ⟨181663522006673105439635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484436058684461614505693 181663522006673105439635)
                  ·
                    refine ⟨272495283010009658159453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181663522006673105439635 272495283010009658159453)
                    ·
                      refine ⟨102185731128753621809795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 272495283010009658159453 102185731128753621809795)
                      ·
                        rfl

theorem cell23_199006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_199006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199006 prefixEnd_199006 := by exact prefixLift 199006
  have htrace : WordTrace (prefixWord ++ tailWord_199006) baseStart_199006 baseEnd_199006 := by
    simpa [prefixWord, tailWord_199006, baseEnd_199006] using wordTrace_append hprefix tailTrace_199006
  have hstable : (prefixWord ++ tailWord_199006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199006).length < 2 ^ (prefixWord ++ tailWord_199006).sum := by decide
  have hdescent : baseEnd_199006 < baseStart_199006 := by decide
  rcases family_descends (prefixWord ++ tailWord_199006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199041 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_199041 : Nat := 118140960795 + 199041 * 2 ^ 59
def prefixEnd_199041 : Nat := 4983230072969 + 3 ^ 40 * 199041 * 2
def baseEnd_199041 : Nat := 102203702951660984872133

theorem tailTrace_199041 : CollatzResearch.WordTrace tailWord_199041 prefixEnd_199041 102203702951660984872133 := by
  unfold tailWord_199041
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259621671915925341548977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4839747781277283561032651 7259621671915925341548977)
  ·
    refine ⟨5444716253936944006161733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7259621671915925341548977 5444716253936944006161733)
    ·
      refine ⟨1020884297613177001155325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5444716253936944006161733 1020884297613177001155325)
      ·
        refine ⟨382831611604941375433247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1020884297613177001155325 382831611604941375433247)
        ·
          refine ⟨574247417407412063149871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382831611604941375433247 574247417407412063149871)
          ·
            refine ⟨861371126111118094724807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574247417407412063149871 861371126111118094724807)
            ·
              refine ⟨1292056689166677142087211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861371126111118094724807 1292056689166677142087211)
              ·
                refine ⟨1938085033750015713130817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292056689166677142087211 1938085033750015713130817)
                ·
                  refine ⟨1453563775312511784848113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1938085033750015713130817 1453563775312511784848113)
                  ·
                    refine ⟨1090172831484383838636085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1453563775312511784848113 1090172831484383838636085)
                    ·
                      refine ⟨102203702951660984872133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1090172831484383838636085 102203702951660984872133)
                      ·
                        rfl

theorem cell23_199041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_199041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199041 prefixEnd_199041 := by exact prefixLift 199041
  have htrace : WordTrace (prefixWord ++ tailWord_199041) baseStart_199041 baseEnd_199041 := by
    simpa [prefixWord, tailWord_199041, baseEnd_199041] using wordTrace_append hprefix tailTrace_199041
  have hstable : (prefixWord ++ tailWord_199041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199041).length < 2 ^ (prefixWord ++ tailWord_199041).sum := by decide
  have hdescent : baseEnd_199041 < baseStart_199041 := by decide
  rcases family_descends (prefixWord ++ tailWord_199041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199071 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 3]
def baseStart_199071 : Nat := 118140960795 + 199071 * 2 ^ 59
def prefixEnd_199071 : Nat := 4983230072969 + 3 ^ 40 * 199071 * 2
def baseEnd_199071 : Nat := 102219107371295867496995

theorem tailTrace_199071 : CollatzResearch.WordTrace tailWord_199071 prefixEnd_199071 102219107371295867496995 := by
  unfold tailWord_199071
  simp only [CollatzResearch.WordTrace]
  refine ⟨7260715861807240465141067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4840477241204826976760711 7260715861807240465141067)
  ·
    refine ⟨10891073792710860697711601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7260715861807240465141067 10891073792710860697711601)
    ·
      refine ⟨8168305344533145523283701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10891073792710860697711601 8168305344533145523283701)
      ·
        refine ⟨765778626049982392807847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8168305344533145523283701 765778626049982392807847)
        ·
          refine ⟨1148667939074973589211771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765778626049982392807847 1148667939074973589211771)
          ·
            refine ⟨1723001908612460383817657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148667939074973589211771 1723001908612460383817657)
            ·
              refine ⟨1292251431459345287863243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723001908612460383817657 1292251431459345287863243)
              ·
                refine ⟨1938377147189017931794865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292251431459345287863243 1938377147189017931794865)
                ·
                  refine ⟨1453782860391763448846149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1938377147189017931794865 1453782860391763448846149)
                  ·
                    refine ⟨272584286323455646658653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453782860391763448846149 272584286323455646658653)
                    ·
                      refine ⟨102219107371295867496995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 272584286323455646658653 102219107371295867496995)
                      ·
                        rfl

theorem cell23_199071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_199071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199071 prefixEnd_199071 := by exact prefixLift 199071
  have htrace : WordTrace (prefixWord ++ tailWord_199071) baseStart_199071 baseEnd_199071 := by
    simpa [prefixWord, tailWord_199071, baseEnd_199071] using wordTrace_append hprefix tailTrace_199071
  have hstable : (prefixWord ++ tailWord_199071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199071).length < 2 ^ (prefixWord ++ tailWord_199071).sum := by decide
  have hdescent : baseEnd_199071 < baseStart_199071 := by decide
  rcases family_descends (prefixWord ++ tailWord_199071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199125 : List Nat := [1, 3, 2, 3, 1, 2, 4, 2, 5]
def baseStart_199125 : Nat := 118140960795 + 199125 * 2 ^ 59
def prefixEnd_199125 : Nat := 4983230072969 + 3 ^ 40 * 199125 * 2
def baseEnd_199125 : Nat := 11360759480737628469083

theorem tailTrace_199125 : CollatzResearch.WordTrace tailWord_199125 prefixEnd_199125 11360759480737628469083 := by
  unfold tailWord_199125
  simp only [CollatzResearch.WordTrace]
  refine ⟨7262685403611607687606829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4841790269074405125071219 7262685403611607687606829)
  ·
    refine ⟨2723507026354352882852561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7262685403611607687606829 2723507026354352882852561)
    ·
      refine ⟨2042630269765764662139421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2723507026354352882852561 2042630269765764662139421)
      ·
        refine ⟨765986351162161748302283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2042630269765764662139421 765986351162161748302283)
        ·
          refine ⟨1148979526743242622453425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765986351162161748302283 1148979526743242622453425)
          ·
            refine ⟨861734645057431966840069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148979526743242622453425 861734645057431966840069)
            ·
              refine ⟨161575245948268493782513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 861734645057431966840069 161575245948268493782513)
              ·
                refine ⟨121181434461201370336885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161575245948268493782513 121181434461201370336885)
                ·
                  refine ⟨11360759480737628469083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121181434461201370336885 11360759480737628469083)
                  ·
                    rfl

theorem cell23_199125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_199125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199125 prefixEnd_199125 := by exact prefixLift 199125
  have htrace : WordTrace (prefixWord ++ tailWord_199125) baseStart_199125 baseEnd_199125 := by
    simpa [prefixWord, tailWord_199125, baseEnd_199125] using wordTrace_append hprefix tailTrace_199125
  have hstable : (prefixWord ++ tailWord_199125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199125).length < 2 ^ (prefixWord ++ tailWord_199125).sum := by decide
  have hdescent : baseEnd_199125 < baseStart_199125 := by decide
  rcases family_descends (prefixWord ++ tailWord_199125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199158 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_199158 : Nat := 118140960795 + 199158 * 2 ^ 59
def prefixEnd_199158 : Nat := 4983230072969 + 3 ^ 40 * 199158 * 2
def baseEnd_199158 : Nat := 102263780188237027109095

theorem tailTrace_199158 : CollatzResearch.WordTrace tailWord_199158 prefixEnd_199158 102263780188237027109095 := by
  unfold tailWord_199158
  simp only [CollatzResearch.WordTrace]
  refine ⟨453993063280753395222383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4842592674994702882372085 453993063280753395222383)
  ·
    refine ⟨680989594921130092833575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 453993063280753395222383 680989594921130092833575)
    ·
      refine ⟨1021484392381695139250363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 680989594921130092833575 1021484392381695139250363)
      ·
        refine ⟨1532226588572542708875545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021484392381695139250363 1532226588572542708875545)
        ·
          refine ⟨1149169941429407031656659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532226588572542708875545 1149169941429407031656659)
          ·
            refine ⟨1723754912144110547484989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149169941429407031656659 1723754912144110547484989)
            ·
              refine ⟨646408092054041455306871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1723754912144110547484989 646408092054041455306871)
              ·
                refine ⟨969612138081062182960307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646408092054041455306871 969612138081062182960307)
                ·
                  refine ⟨1454418207121593274440461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969612138081062182960307 1454418207121593274440461)
                  ·
                    refine ⟨545406827670597477915173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454418207121593274440461 545406827670597477915173)
                    ·
                      refine ⟨102263780188237027109095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 545406827670597477915173 102263780188237027109095)
                      ·
                        rfl

theorem cell23_199158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_199158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199158 prefixEnd_199158 := by exact prefixLift 199158
  have htrace : WordTrace (prefixWord ++ tailWord_199158) baseStart_199158 baseEnd_199158 := by
    simpa [prefixWord, tailWord_199158, baseEnd_199158] using wordTrace_append hprefix tailTrace_199158
  have hstable : (prefixWord ++ tailWord_199158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199158).length < 2 ^ (prefixWord ++ tailWord_199158).sum := by decide
  have hdescent : baseEnd_199158 < baseStart_199158 := by decide
  rcases family_descends (prefixWord ++ tailWord_199158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199178 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_199178 : Nat := 118140960795 + 199178 * 2 ^ 59
def prefixEnd_199178 : Nat := 4983230072969 + 3 ^ 40 * 199178 * 2
def baseEnd_199178 : Nat := 102274049801326948859003

theorem tailTrace_199178 : CollatzResearch.WordTrace tailWord_199178 prefixEnd_199178 102274049801326948859003 := by
  unfold tailWord_199178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816154618104899434821547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4843078981613065159524125 1816154618104899434821547)
  ·
    refine ⟨2724231927157349152232321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1816154618104899434821547 2724231927157349152232321)
    ·
      refine ⟨2043173945368011864174241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2724231927157349152232321 2043173945368011864174241)
      ·
        refine ⟨1532380459026008898130681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2043173945368011864174241 1532380459026008898130681)
        ·
          refine ⟨1149285344269506673598011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532380459026008898130681 1149285344269506673598011)
          ·
            refine ⟨1723928016404260010397017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149285344269506673598011 1723928016404260010397017)
            ·
              refine ⟨1292946012303195007797763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723928016404260010397017 1292946012303195007797763)
              ·
                refine ⟨1939419018454792511696645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292946012303195007797763 1939419018454792511696645)
                ·
                  refine ⟨363641065960273595943121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939419018454792511696645 363641065960273595943121)
                  ·
                    refine ⟨272730799470205196957341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 363641065960273595943121 272730799470205196957341)
                    ·
                      refine ⟨102274049801326948859003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 272730799470205196957341 102274049801326948859003)
                      ·
                        rfl

theorem cell23_199178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_199178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199178 prefixEnd_199178 := by exact prefixLift 199178
  have htrace : WordTrace (prefixWord ++ tailWord_199178) baseStart_199178 baseEnd_199178 := by
    simpa [prefixWord, tailWord_199178, baseEnd_199178] using wordTrace_append hprefix tailTrace_199178
  have hstable : (prefixWord ++ tailWord_199178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199178).length < 2 ^ (prefixWord ++ tailWord_199178).sum := by decide
  have hdescent : baseEnd_199178 < baseStart_199178 := by decide
  rcases family_descends (prefixWord ++ tailWord_199178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199201 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_199201 : Nat := 118140960795 + 199201 * 2 ^ 59
def prefixEnd_199201 : Nat := 4983230072969 + 3 ^ 40 * 199201 * 2
def baseEnd_199201 : Nat := 102285859856380358871397

theorem tailTrace_199201 : CollatzResearch.WordTrace tailWord_199201 prefixEnd_199201 102285859856380358871397 := by
  unfold tailWord_199201
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265457351336272667373457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4843638234224181778248971 7265457351336272667373457)
  ·
    refine ⟨5449093013502204500530093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7265457351336272667373457 5449093013502204500530093)
    ·
      refine ⟨2043409880063326687698785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5449093013502204500530093 2043409880063326687698785)
      ·
        refine ⟨1532557410047495015774089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2043409880063326687698785 1532557410047495015774089)
        ·
          refine ⟨1149418057535621261830567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532557410047495015774089 1149418057535621261830567)
          ·
            refine ⟨1724127086303431892745851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149418057535621261830567 1724127086303431892745851)
            ·
              refine ⟨2586190629455147839118777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724127086303431892745851 2586190629455147839118777)
              ·
                refine ⟨1939642972091360879339083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2586190629455147839118777 1939642972091360879339083)
                ·
                  refine ⟨2909464458137041319008625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939642972091360879339083 2909464458137041319008625)
                  ·
                    refine ⟨2182098343602780989256469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2909464458137041319008625 2182098343602780989256469)
                    ·
                      refine ⟨102285859856380358871397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2182098343602780989256469 102285859856380358871397)
                      ·
                        rfl

theorem cell23_199201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_199201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199201 prefixEnd_199201 := by exact prefixLift 199201
  have htrace : WordTrace (prefixWord ++ tailWord_199201) baseStart_199201 baseEnd_199201 := by
    simpa [prefixWord, tailWord_199201, baseEnd_199201] using wordTrace_append hprefix tailTrace_199201
  have hstable : (prefixWord ++ tailWord_199201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199201).length < 2 ^ (prefixWord ++ tailWord_199201).sum := by decide
  have hdescent : baseEnd_199201 < baseStart_199201 := by decide
  rcases family_descends (prefixWord ++ tailWord_199201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199211 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 3, 5]
def baseStart_199211 : Nat := 118140960795 + 199211 * 2 ^ 59
def prefixEnd_199211 : Nat := 4983230072969 + 3 ^ 40 * 199211 * 2
def baseEnd_199211 : Nat := 34096998220975106582117

theorem tailTrace_199211 : CollatzResearch.WordTrace tailWord_199211 prefixEnd_199211 34096998220975106582117 := by
  unfold tailWord_199211
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265822081300044375237487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4843881387533362916824991 7265822081300044375237487)
  ·
    refine ⟨10898733121950066562856231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7265822081300044375237487 10898733121950066562856231)
    ·
      refine ⟨16348099682925099844284347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10898733121950066562856231 16348099682925099844284347)
      ·
        refine ⟨24522149524387649766426521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16348099682925099844284347 24522149524387649766426521)
        ·
          refine ⟨18391612143290737324819891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24522149524387649766426521 18391612143290737324819891)
          ·
            refine ⟨27587418214936105987229837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18391612143290737324819891 27587418214936105987229837)
            ·
              refine ⟨10345281830601039745211189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27587418214936105987229837 10345281830601039745211189)
              ·
                refine ⟨969870171618847476113549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10345281830601039745211189 969870171618847476113549)
                ·
                  refine ⟨363701314357067803542581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969870171618847476113549 363701314357067803542581)
                  ·
                    refine ⟨34096998220975106582117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 363701314357067803542581 34096998220975106582117)
                    ·
                      rfl

theorem cell23_199211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 5].length) (baseStart_199211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199211 prefixEnd_199211 := by exact prefixLift 199211
  have htrace : WordTrace (prefixWord ++ tailWord_199211) baseStart_199211 baseEnd_199211 := by
    simpa [prefixWord, tailWord_199211, baseEnd_199211] using wordTrace_append hprefix tailTrace_199211
  have hstable : (prefixWord ++ tailWord_199211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199211).length < 2 ^ (prefixWord ++ tailWord_199211).sum := by decide
  have hdescent : baseEnd_199211 < baseStart_199211 := by decide
  rcases family_descends (prefixWord ++ tailWord_199211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199236 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_199236 : Nat := 118140960795 + 199236 * 2 ^ 59
def prefixEnd_199236 : Nat := 4983230072969 + 3 ^ 40 * 199236 * 2
def baseEnd_199236 : Nat := 34101277226429240644579

theorem tailTrace_199236 : CollatzResearch.WordTrace tailWord_199236 prefixEnd_199236 34101277226429240644579 := by
  unfold tailWord_199236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633366953104736822448781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4844489270806315763265041 3633366953104736822448781)
  ·
    refine ⟨1362512607414276308418293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3633366953104736822448781 1362512607414276308418293)
    ·
      refine ⟨127735556945088403914215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1362512607414276308418293 127735556945088403914215)
      ·
        refine ⟨191603335417632605871323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127735556945088403914215 191603335417632605871323)
        ·
          refine ⟨287405003126448908806985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191603335417632605871323 287405003126448908806985)
          ·
            refine ⟨215553752344836681605239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287405003126448908806985 215553752344836681605239)
            ·
              refine ⟨323330628517255022407859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215553752344836681605239 323330628517255022407859)
              ·
                refine ⟨484995942775882533611789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323330628517255022407859 484995942775882533611789)
                ·
                  refine ⟨181873478540955950104421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484995942775882533611789 181873478540955950104421)
                  ·
                    refine ⟨34101277226429240644579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181873478540955950104421 34101277226429240644579)
                    ·
                      rfl

theorem cell23_199236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_199236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199236 prefixEnd_199236 := by exact prefixLift 199236
  have htrace : WordTrace (prefixWord ++ tailWord_199236) baseStart_199236 baseEnd_199236 := by
    simpa [prefixWord, tailWord_199236, baseEnd_199236] using wordTrace_append hprefix tailTrace_199236
  have hstable : (prefixWord ++ tailWord_199236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199236).length < 2 ^ (prefixWord ++ tailWord_199236).sum := by decide
  have hdescent : baseEnd_199236 < baseStart_199236 := by decide
  rcases family_descends (prefixWord ++ tailWord_199236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199242 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_199242 : Nat := 118140960795 + 199242 * 2 ^ 59
def prefixEnd_199242 : Nat := 4983230072969 + 3 ^ 40 * 199242 * 2
def baseEnd_199242 : Nat := 102306912563214698458709

theorem tailTrace_199242 : CollatzResearch.WordTrace tailWord_199242 prefixEnd_199242 102306912563214698458709 := by
  unfold tailWord_199242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816738186046934167403995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4844635162791824446410653 1816738186046934167403995)
  ·
    refine ⟨2725107279070401251105993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1816738186046934167403995 2725107279070401251105993)
    ·
      refine ⟨2043830459302800938329495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2725107279070401251105993 2043830459302800938329495)
      ·
        refine ⟨3065745688954201407494243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043830459302800938329495 3065745688954201407494243)
        ·
          refine ⟨4598618533431302111241365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065745688954201407494243 4598618533431302111241365)
          ·
            refine ⟨215560243754592286464439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4598618533431302111241365 215560243754592286464439)
            ·
              refine ⟨323340365631888429696659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215560243754592286464439 323340365631888429696659)
              ·
                refine ⟨485010548447832644544989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323340365631888429696659 485010548447832644544989)
                ·
                  refine ⟨181878955667937241704371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485010548447832644544989 181878955667937241704371)
                  ·
                    refine ⟨272818433501905862556557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181878955667937241704371 272818433501905862556557)
                    ·
                      refine ⟨102306912563214698458709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 272818433501905862556557 102306912563214698458709)
                      ·
                        rfl

theorem cell23_199242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_199242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199242 prefixEnd_199242 := by exact prefixLift 199242
  have htrace : WordTrace (prefixWord ++ tailWord_199242) baseStart_199242 baseEnd_199242 := by
    simpa [prefixWord, tailWord_199242, baseEnd_199242] using wordTrace_append hprefix tailTrace_199242
  have hstable : (prefixWord ++ tailWord_199242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199242).length < 2 ^ (prefixWord ++ tailWord_199242).sum := by decide
  have hdescent : baseEnd_199242 < baseStart_199242 := by decide
  rcases family_descends (prefixWord ++ tailWord_199242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199248 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 2, 6, 2]
def baseStart_199248 : Nat := 118140960795 + 199248 * 2 ^ 59
def prefixEnd_199248 : Nat := 4983230072969 + 3 ^ 40 * 199248 * 2
def baseEnd_199248 : Nat := 102309993447141674983681

theorem tailTrace_199248 : CollatzResearch.WordTrace tailWord_199248 prefixEnd_199248 102309993447141674983681 := by
  unfold tailWord_199248
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633585791082999847167199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4844781054777333129556265 3633585791082999847167199)
  ·
    refine ⟨5450378686624499770750799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3633585791082999847167199 5450378686624499770750799)
    ·
      refine ⟨8175568029936749656126199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5450378686624499770750799 8175568029936749656126199)
      ·
        refine ⟨12263352044905124484189299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8175568029936749656126199 12263352044905124484189299)
        ·
          refine ⟨18395028067357686726283949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12263352044905124484189299 18395028067357686726283949)
          ·
            refine ⟨6898135525259132522356481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18395028067357686726283949 6898135525259132522356481)
            ·
              refine ⟨5173601643944349391767361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6898135525259132522356481 5173601643944349391767361)
              ·
                refine ⟨3880201232958262043825521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5173601643944349391767361 3880201232958262043825521)
                ·
                  refine ⟨2910150924718696532869141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880201232958262043825521 2910150924718696532869141)
                  ·
                    refine ⟨136413324596188899978241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2910150924718696532869141 136413324596188899978241)
                    ·
                      refine ⟨102309993447141674983681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136413324596188899978241 102309993447141674983681)
                      ·
                        rfl

theorem cell23_199248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 6, 2].length) (baseStart_199248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199248 prefixEnd_199248 := by exact prefixLift 199248
  have htrace : WordTrace (prefixWord ++ tailWord_199248) baseStart_199248 baseEnd_199248 := by
    simpa [prefixWord, tailWord_199248, baseEnd_199248] using wordTrace_append hprefix tailTrace_199248
  have hstable : (prefixWord ++ tailWord_199248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199248).length < 2 ^ (prefixWord ++ tailWord_199248).sum := by decide
  have hdescent : baseEnd_199248 < baseStart_199248 := by decide
  rcases family_descends (prefixWord ++ tailWord_199248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199265 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_199265 : Nat := 118140960795 + 199265 * 2 ^ 59
def prefixEnd_199265 : Nat := 4983230072969 + 3 ^ 40 * 199265 * 2
def baseEnd_199265 : Nat := 102318722618268108471103

theorem tailTrace_199265 : CollatzResearch.WordTrace tailWord_199265 prefixEnd_199265 102318722618268108471103 := by
  unfold tailWord_199265
  simp only [CollatzResearch.WordTrace]
  refine ⟨7267791623104411597703249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4845194415402941065135499 7267791623104411597703249)
  ·
    refine ⟨5450843717328308698277437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7267791623104411597703249 5450843717328308698277437)
    ·
      refine ⟨2044066393998115761854039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5450843717328308698277437 2044066393998115761854039)
      ·
        refine ⟨3066099590997173642781059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044066393998115761854039 3066099590997173642781059)
        ·
          refine ⟨4599149386495760464171589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066099590997173642781059 4599149386495760464171589)
          ·
            refine ⟨862340509967955087032173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4599149386495760464171589 862340509967955087032173)
            ·
              refine ⟨323377691237983157637065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 862340509967955087032173 323377691237983157637065)
              ·
                refine ⟨242533268428487368227799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323377691237983157637065 242533268428487368227799)
                ·
                  refine ⟨363799902642731052341699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242533268428487368227799 363799902642731052341699)
                  ·
                    refine ⟨545699853964096578512549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 363799902642731052341699 545699853964096578512549)
                    ·
                      refine ⟨102318722618268108471103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 545699853964096578512549 102318722618268108471103)
                      ·
                        rfl

theorem cell23_199265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_199265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199265 prefixEnd_199265 := by exact prefixLift 199265
  have htrace : WordTrace (prefixWord ++ tailWord_199265) baseStart_199265 baseEnd_199265 := by
    simpa [prefixWord, tailWord_199265, baseEnd_199265] using wordTrace_append hprefix tailTrace_199265
  have hstable : (prefixWord ++ tailWord_199265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199265).length < 2 ^ (prefixWord ++ tailWord_199265).sum := by decide
  have hdescent : baseEnd_199265 < baseStart_199265 := by decide
  rcases family_descends (prefixWord ++ tailWord_199265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199291 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 6]
def baseStart_199291 : Nat := 118140960795 + 199291 * 2 ^ 59
def prefixEnd_199291 : Nat := 4983230072969 + 3 ^ 40 * 199291 * 2
def baseEnd_199291 : Nat := 102332073115285006745983

theorem tailTrace_199291 : CollatzResearch.WordTrace tailWord_199291 prefixEnd_199291 102332073115285006745983 := by
  unfold tailWord_199291
  simp only [CollatzResearch.WordTrace]
  refine ⟨7268739921010218038149727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4845826614006812025433151 7268739921010218038149727)
  ·
    refine ⟨10903109881515327057224591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7268739921010218038149727 10903109881515327057224591)
    ·
      refine ⟨16354664822272990585836887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10903109881515327057224591 16354664822272990585836887)
      ·
        refine ⟨24531997233409485878755331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16354664822272990585836887 24531997233409485878755331)
        ·
          refine ⟨36797995850114228818132997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24531997233409485878755331 36797995850114228818132997)
          ·
            refine ⟨6899624221896417903399937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36797995850114228818132997 6899624221896417903399937)
            ·
              refine ⟨5174718166422313427549953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6899624221896417903399937 5174718166422313427549953)
              ·
                refine ⟨3881038624816735070662465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5174718166422313427549953 3881038624816735070662465)
                ·
                  refine ⟨2910778968612551302996849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3881038624816735070662465 2910778968612551302996849)
                  ·
                    refine ⟨2183084226459413477247637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2910778968612551302996849 2183084226459413477247637)
                    ·
                      refine ⟨102332073115285006745983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2183084226459413477247637 102332073115285006745983)
                      ·
                        rfl

theorem cell23_199291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_199291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199291 prefixEnd_199291 := by exact prefixLift 199291
  have htrace : WordTrace (prefixWord ++ tailWord_199291) baseStart_199291 baseEnd_199291 := by
    simpa [prefixWord, tailWord_199291, baseEnd_199291] using wordTrace_append hprefix tailTrace_199291
  have hstable : (prefixWord ++ tailWord_199291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199291).length < 2 ^ (prefixWord ++ tailWord_199291).sum := by decide
  have hdescent : baseEnd_199291 < baseStart_199291 := by decide
  rcases family_descends (prefixWord ++ tailWord_199291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199293 : List Nat := [1, 4, 1, 1, 6, 1, 2, 2, 1, 1, 3]
def baseStart_199293 : Nat := 118140960795 + 199293 * 2 ^ 59
def prefixEnd_199293 : Nat := 4983230072969 + 3 ^ 40 * 199293 * 2
def baseEnd_199293 : Nat := 102333100076593998920975

theorem tailTrace_199293 : CollatzResearch.WordTrace tailWord_199293 prefixEnd_199293 102333100076593998920975 := by
  unfold tailWord_199293
  simp only [CollatzResearch.WordTrace]
  refine ⟨7268812867002972379722533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4845875244668648253148355 7268812867002972379722533)
  ·
    refine ⟨1362902412563057321197975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7268812867002972379722533 1362902412563057321197975)
    ·
      refine ⟨2044353618844585981796963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1362902412563057321197975 2044353618844585981796963)
      ·
        refine ⟨3066530428266878972695445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044353618844585981796963 3066530428266878972695445)
        ·
          refine ⟨143743613825009951845099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3066530428266878972695445 143743613825009951845099)
          ·
            refine ⟨215615420737514927767649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143743613825009951845099 215615420737514927767649)
            ·
              refine ⟨161711565553136195825737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215615420737514927767649 161711565553136195825737)
              ·
                refine ⟨121283674164852146869303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161711565553136195825737 121283674164852146869303)
                ·
                  refine ⟨181925511247278220303955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121283674164852146869303 181925511247278220303955)
                  ·
                    refine ⟨272888266870917330455933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181925511247278220303955 272888266870917330455933)
                    ·
                      refine ⟨102333100076593998920975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 272888266870917330455933 102333100076593998920975)
                      ·
                        rfl

theorem cell23_199293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_199293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199293 prefixEnd_199293 := by exact prefixLift 199293
  have htrace : WordTrace (prefixWord ++ tailWord_199293) baseStart_199293 baseEnd_199293 := by
    simpa [prefixWord, tailWord_199293, baseEnd_199293] using wordTrace_append hprefix tailTrace_199293
  have hstable : (prefixWord ++ tailWord_199293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199293).length < 2 ^ (prefixWord ++ tailWord_199293).sum := by decide
  have hdescent : baseEnd_199293 < baseStart_199293 := by decide
  rcases family_descends (prefixWord ++ tailWord_199293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199322 : List Nat := [3, 1, 1, 6, 1, 1, 3, 7]
def baseStart_199322 : Nat := 118140960795 + 199322 * 2 ^ 59
def prefixEnd_199322 : Nat := 4983230072969 + 3 ^ 40 * 199322 * 2
def baseEnd_199322 : Nat := 3790666333910162424383

theorem tailTrace_199322 : CollatzResearch.WordTrace tailWord_199322 prefixEnd_199322 3790666333910162424383 := by
  unfold tailWord_199322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817467645974477583132055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4846580389265273555018813 1817467645974477583132055)
  ·
    refine ⟨2726201468961716374698083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1817467645974477583132055 2726201468961716374698083)
    ·
      refine ⟨4089302203442574562047125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2726201468961716374698083 4089302203442574562047125)
      ·
        refine ⟨191686040786370682595959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4089302203442574562047125 191686040786370682595959)
        ·
          refine ⟨287529061179556023893939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191686040786370682595959 287529061179556023893939)
          ·
            refine ⟨431293591769334035840909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287529061179556023893939 431293591769334035840909)
            ·
              refine ⟨161735096913500263440341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431293591769334035840909 161735096913500263440341)
              ·
                refine ⟨3790666333910162424383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161735096913500263440341 3790666333910162424383)
                ·
                  rfl

theorem cell23_199322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 7].length) (baseStart_199322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199322 prefixEnd_199322 := by exact prefixLift 199322
  have htrace : WordTrace (prefixWord ++ tailWord_199322) baseStart_199322 baseEnd_199322 := by
    simpa [prefixWord, tailWord_199322, baseEnd_199322] using wordTrace_append hprefix tailTrace_199322
  have hstable : (prefixWord ++ tailWord_199322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199322).length < 2 ^ (prefixWord ++ tailWord_199322).sum := by decide
  have hdescent : baseEnd_199322 < baseStart_199322 := by decide
  rcases family_descends (prefixWord ++ tailWord_199322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199349 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_199349 : Nat := 118140960795 + 199349 * 2 ^ 59
def prefixEnd_199349 : Nat := 4983230072969 + 3 ^ 40 * 199349 * 2
def baseEnd_199349 : Nat := 102361854993245779820717

theorem tailTrace_199349 : CollatzResearch.WordTrace tailWord_199349 prefixEnd_199349 102361854993245779820717 := by
  unfold tailWord_199349
  simp only [CollatzResearch.WordTrace]
  refine ⟨7270855354800093943761101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4847236903200062629174067 7270855354800093943761101)
  ·
    refine ⟨2726570758050035228910413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7270855354800093943761101 2726570758050035228910413)
    ·
      refine ⟨1022464034268763210841405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2726570758050035228910413 1022464034268763210841405)
      ·
        refine ⟨383424012850786204065527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1022464034268763210841405 383424012850786204065527)
        ·
          refine ⟨575136019276179306098291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383424012850786204065527 575136019276179306098291)
          ·
            refine ⟨862704028914268959147437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575136019276179306098291 862704028914268959147437)
            ·
              refine ⟨323514010842850859680289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 862704028914268959147437 323514010842850859680289)
              ·
                refine ⟨242635508132138144760217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323514010842850859680289 242635508132138144760217)
                ·
                  refine ⟨181976631099103608570163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242635508132138144760217 181976631099103608570163)
                  ·
                    refine ⟨272964946648655412855245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181976631099103608570163 272964946648655412855245)
                    ·
                      refine ⟨102361854993245779820717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 272964946648655412855245 102361854993245779820717)
                      ·
                        rfl

theorem cell23_199349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_199349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199349 prefixEnd_199349 := by exact prefixLift 199349
  have htrace : WordTrace (prefixWord ++ tailWord_199349) baseStart_199349 baseEnd_199349 := by
    simpa [prefixWord, tailWord_199349, baseEnd_199349] using wordTrace_append hprefix tailTrace_199349
  have hstable : (prefixWord ++ tailWord_199349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199349).length < 2 ^ (prefixWord ++ tailWord_199349).sum := by decide
  have hdescent : baseEnd_199349 < baseStart_199349 := by decide
  rcases family_descends (prefixWord ++ tailWord_199349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199415 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 2, 5, 2]
def baseStart_199415 : Nat := 118140960795 + 199415 * 2 ^ 59
def prefixEnd_199415 : Nat := 4983230072969 + 3 ^ 40 * 199415 * 2
def baseEnd_199415 : Nat := 102395744716442521595413

theorem tailTrace_199415 : CollatzResearch.WordTrace tailWord_199415 prefixEnd_199415 102395744716442521595413 := by
  unfold tailWord_199415
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273262572560987215663699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4848841715040658143775799 7273262572560987215663699)
  ·
    refine ⟨10909893858841480823495549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7273262572560987215663699 10909893858841480823495549)
    ·
      refine ⟨4091210197065555308810831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10909893858841480823495549 4091210197065555308810831)
      ·
        refine ⟨6136815295598332963216247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091210197065555308810831 6136815295598332963216247)
        ·
          refine ⟨9205222943397499444824371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136815295598332963216247 9205222943397499444824371)
          ·
            refine ⟨13807834415096249167236557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9205222943397499444824371 13807834415096249167236557)
            ·
              refine ⟨5177937905661093437713709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13807834415096249167236557 5177937905661093437713709)
              ·
                refine ⟨1941726714622910039142641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5177937905661093437713709 1941726714622910039142641)
                ·
                  refine ⟨1456295035967182529356981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1941726714622910039142641 1456295035967182529356981)
                  ·
                    refine ⟨136527659621923362127217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1456295035967182529356981 136527659621923362127217)
                    ·
                      refine ⟨102395744716442521595413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136527659621923362127217 102395744716442521595413)
                      ·
                        rfl

theorem cell23_199415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_199415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199415 prefixEnd_199415 := by exact prefixLift 199415
  have htrace : WordTrace (prefixWord ++ tailWord_199415) baseStart_199415 baseEnd_199415 := by
    simpa [prefixWord, tailWord_199415, baseEnd_199415] using wordTrace_append hprefix tailTrace_199415
  have hstable : (prefixWord ++ tailWord_199415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199415).length < 2 ^ (prefixWord ++ tailWord_199415).sum := by decide
  have hdescent : baseEnd_199415 < baseStart_199415 := by decide
  rcases family_descends (prefixWord ++ tailWord_199415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199418 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_199418 : Nat := 118140960795 + 199418 * 2 ^ 59
def prefixEnd_199418 : Nat := 4983230072969 + 3 ^ 40 * 199418 * 2
def baseEnd_199418 : Nat := 102397285158406009857899

theorem tailTrace_199418 : CollatzResearch.WordTrace tailWord_199418 prefixEnd_199418 102397285158406009857899 := by
  unfold tailWord_199418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1818342997887529682005727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4848914661033412485348605 1818342997887529682005727)
  ·
    refine ⟨2727514496831294523008591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1818342997887529682005727 2727514496831294523008591)
    ·
      refine ⟨4091271745246941784512887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2727514496831294523008591 4091271745246941784512887)
      ·
        refine ⟨6136907617870412676769331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091271745246941784512887 6136907617870412676769331)
        ·
          refine ⟨9205361426805619015153997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136907617870412676769331 9205361426805619015153997)
          ·
            refine ⟨3452010535052107130682749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9205361426805619015153997 3452010535052107130682749)
            ·
              refine ⟨1294503950644540174006031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3452010535052107130682749 1294503950644540174006031)
              ·
                refine ⟨1941755925966810261009047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294503950644540174006031 1941755925966810261009047)
                ·
                  refine ⟨2912633888950215391513571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941755925966810261009047 2912633888950215391513571)
                  ·
                    refine ⟨4368950833425323087270357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2912633888950215391513571 4368950833425323087270357)
                    ·
                      refine ⟨102397285158406009857899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4368950833425323087270357 102397285158406009857899)
                      ·
                        rfl

theorem cell23_199418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_199418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199418 prefixEnd_199418 := by exact prefixLift 199418
  have htrace : WordTrace (prefixWord ++ tailWord_199418) baseStart_199418 baseEnd_199418 := by
    simpa [prefixWord, tailWord_199418, baseEnd_199418] using wordTrace_append hprefix tailTrace_199418
  have hstable : (prefixWord ++ tailWord_199418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199418).length < 2 ^ (prefixWord ++ tailWord_199418).sum := by decide
  have hdescent : baseEnd_199418 < baseStart_199418 := by decide
  rcases family_descends (prefixWord ++ tailWord_199418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199535 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_199535 : Nat := 118140960795 + 199535 * 2 ^ 59
def prefixEnd_199535 : Nat := 4983230072969 + 3 ^ 40 * 199535 * 2
def baseEnd_199535 : Nat := 102457362394982052094861

theorem tailTrace_199535 : CollatzResearch.WordTrace tailWord_199535 prefixEnd_199535 102457362394982052094861 := by
  unfold tailWord_199535
  simp only [CollatzResearch.WordTrace]
  refine ⟨7277639332126247710032059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4851759554750831806688039 7277639332126247710032059)
  ·
    refine ⟨10916458998189371565048089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7277639332126247710032059 10916458998189371565048089)
    ·
      refine ⟨8187344248642028673786067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10916458998189371565048089 8187344248642028673786067)
      ·
        refine ⟨12281016372963043010679101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8187344248642028673786067 12281016372963043010679101)
        ·
          refine ⟨4605381139861141129004663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12281016372963043010679101 4605381139861141129004663)
          ·
            refine ⟨6908071709791711693506995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605381139861141129004663 6908071709791711693506995)
            ·
              refine ⟨10362107564687567540260493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908071709791711693506995 10362107564687567540260493)
              ·
                refine ⟨3885790336757837827597685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10362107564687567540260493 3885790336757837827597685)
                ·
                  refine ⟨364292844071047296337283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3885790336757837827597685 364292844071047296337283)
                  ·
                    refine ⟨546439266106570944505925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 364292844071047296337283 546439266106570944505925)
                    ·
                      refine ⟨102457362394982052094861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 546439266106570944505925 102457362394982052094861)
                      ·
                        rfl

theorem cell23_199535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_199535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199535 prefixEnd_199535 := by exact prefixLift 199535
  have htrace : WordTrace (prefixWord ++ tailWord_199535) baseStart_199535 baseEnd_199535 := by
    simpa [prefixWord, tailWord_199535, baseEnd_199535] using wordTrace_append hprefix tailTrace_199535
  have hstable : (prefixWord ++ tailWord_199535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199535).length < 2 ^ (prefixWord ++ tailWord_199535).sum := by decide
  have hdescent : baseEnd_199535 < baseStart_199535 := by decide
  rcases family_descends (prefixWord ++ tailWord_199535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199555 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 5]
def baseStart_199555 : Nat := 118140960795 + 199555 * 2 ^ 59
def prefixEnd_199555 : Nat := 4983230072969 + 3 ^ 40 * 199555 * 2
def baseEnd_199555 : Nat := 102467632008071973844769

theorem tailTrace_199555 : CollatzResearch.WordTrace tailWord_199555 prefixEnd_199555 102467632008071973844769 := by
  unfold tailWord_199555
  simp only [CollatzResearch.WordTrace]
  refine ⟨7278368792053791125760119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4852245861369194083840079 7278368792053791125760119)
  ·
    refine ⟨10917553188080686688640179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7278368792053791125760119 10917553188080686688640179)
    ·
      refine ⟨16376329782121030032960269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10917553188080686688640179 16376329782121030032960269)
      ·
        refine ⟨6141123668295386262360101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16376329782121030032960269 6141123668295386262360101)
        ·
          refine ⟨1151460687805384924192519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6141123668295386262360101 1151460687805384924192519)
          ·
            refine ⟨1727191031708077386288779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151460687805384924192519 1727191031708077386288779)
            ·
              refine ⟨2590786547562116079433169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727191031708077386288779 2590786547562116079433169)
              ·
                refine ⟨1943089910671587059574877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590786547562116079433169 1943089910671587059574877)
                ·
                  refine ⟨728658716501845147340579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1943089910671587059574877 728658716501845147340579)
                  ·
                    refine ⟨1092988074752767721010869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 728658716501845147340579 1092988074752767721010869)
                    ·
                      refine ⟨102467632008071973844769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1092988074752767721010869 102467632008071973844769)
                      ·
                        rfl

theorem cell23_199555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_199555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199555 prefixEnd_199555 := by exact prefixLift 199555
  have htrace : WordTrace (prefixWord ++ tailWord_199555) baseStart_199555 baseEnd_199555 := by
    simpa [prefixWord, tailWord_199555, baseEnd_199555] using wordTrace_append hprefix tailTrace_199555
  have hstable : (prefixWord ++ tailWord_199555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199555).length < 2 ^ (prefixWord ++ tailWord_199555).sum := by decide
  have hdescent : baseEnd_199555 < baseStart_199555 := by decide
  rcases family_descends (prefixWord ++ tailWord_199555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199580 : List Nat := [2, 2, 3, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_199580 : Nat := 118140960795 + 199580 * 2 ^ 59
def prefixEnd_199580 : Nat := 4983230072969 + 3 ^ 40 * 199580 * 2
def baseEnd_199580 : Nat := 102480469024434376032155

theorem tailTrace_199580 : CollatzResearch.WordTrace tailWord_199580 prefixEnd_199580 102480469024434376032155 := by
  unfold tailWord_199580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3639640308481610197710097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4852853744642146930280129 3639640308481610197710097)
  ·
    refine ⟨2729730231361207648282573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3639640308481610197710097 2729730231361207648282573)
    ·
      refine ⟨1023648836760452868105965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2729730231361207648282573 1023648836760452868105965)
      ·
        refine ⟨383868313785169825539737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1023648836760452868105965 383868313785169825539737)
        ·
          refine ⟨287901235338877369154803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383868313785169825539737 287901235338877369154803)
          ·
            refine ⟨431851853008316053732205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287901235338877369154803 431851853008316053732205)
            ·
              refine ⟨161944444878118520149577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431851853008316053732205 161944444878118520149577)
              ·
                refine ⟨121458333658588890112183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161944444878118520149577 121458333658588890112183)
                ·
                  refine ⟨182187500487883335168275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121458333658588890112183 182187500487883335168275)
                  ·
                    refine ⟨273281250731825002752413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182187500487883335168275 273281250731825002752413)
                    ·
                      refine ⟨102480469024434376032155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 273281250731825002752413 102480469024434376032155)
                      ·
                        rfl

theorem cell23_199580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_199580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199580 prefixEnd_199580 := by exact prefixLift 199580
  have htrace : WordTrace (prefixWord ++ tailWord_199580) baseStart_199580 baseEnd_199580 := by
    simpa [prefixWord, tailWord_199580, baseEnd_199580] using wordTrace_append hprefix tailTrace_199580
  have hstable : (prefixWord ++ tailWord_199580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199580).length < 2 ^ (prefixWord ++ tailWord_199580).sum := by decide
  have hdescent : baseEnd_199580 < baseStart_199580 := by decide
  rcases family_descends (prefixWord ++ tailWord_199580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199615 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_199615 : Nat := 118140960795 + 199615 * 2 ^ 59
def prefixEnd_199615 : Nat := 4983230072969 + 3 ^ 40 * 199615 * 2
def baseEnd_199615 : Nat := 102498440847341739094493

theorem tailTrace_199615 : CollatzResearch.WordTrace tailWord_199615 prefixEnd_199615 102498440847341739094493 := by
  unfold tailWord_199615
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280557171836421372944299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4853704781224280915296199 7280557171836421372944299)
  ·
    refine ⟨10920835757754632059416449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7280557171836421372944299 10920835757754632059416449)
    ·
      refine ⟨8190626818315974044562337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10920835757754632059416449 8190626818315974044562337)
      ·
        refine ⟨6142970113736980533421753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8190626818315974044562337 6142970113736980533421753)
        ·
          refine ⟨4607227585302735400066315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6142970113736980533421753 4607227585302735400066315)
          ·
            refine ⟨6910841377954103100099473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607227585302735400066315 6910841377954103100099473)
            ·
              refine ⟨5183131033465577325074605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6910841377954103100099473 5183131033465577325074605)
              ·
                refine ⟨1943674137549591496902977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5183131033465577325074605 1943674137549591496902977)
                ·
                  refine ⟨1457755603162193622677233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1943674137549591496902977 1457755603162193622677233)
                  ·
                    refine ⟨1093316702371645217007925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457755603162193622677233 1093316702371645217007925)
                    ·
                      refine ⟨102498440847341739094493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1093316702371645217007925 102498440847341739094493)
                      ·
                        rfl

theorem cell23_199615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_199615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199615 prefixEnd_199615 := by exact prefixLift 199615
  have htrace : WordTrace (prefixWord ++ tailWord_199615) baseStart_199615 baseEnd_199615 := by
    simpa [prefixWord, tailWord_199615, baseEnd_199615] using wordTrace_append hprefix tailTrace_199615
  have hstable : (prefixWord ++ tailWord_199615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199615).length < 2 ^ (prefixWord ++ tailWord_199615).sum := by decide
  have hdescent : baseEnd_199615 < baseStart_199615 := by decide
  rcases family_descends (prefixWord ++ tailWord_199615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199625 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_199625 : Nat := 118140960795 + 199625 * 2 ^ 59
def prefixEnd_199625 : Nat := 4983230072969 + 3 ^ 40 * 199625 * 2
def baseEnd_199625 : Nat := 102503575653886699969447

theorem tailTrace_199625 : CollatzResearch.WordTrace tailWord_199625 prefixEnd_199625 102503575653886699969447 := by
  unfold tailWord_199625
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280921901800193080808329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4853947934533462053872219 7280921901800193080808329)
  ·
    refine ⟨5460691426350144810606247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7280921901800193080808329 5460691426350144810606247)
    ·
      refine ⟨8191037139525217215909371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5460691426350144810606247 8191037139525217215909371)
      ·
        refine ⟨12286555709287825823864057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8191037139525217215909371 12286555709287825823864057)
        ·
          refine ⟨9214916781965869367898043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12286555709287825823864057 9214916781965869367898043)
          ·
            refine ⟨13822375172948804051847065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9214916781965869367898043 13822375172948804051847065)
            ·
              refine ⟨10366781379711603038885299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13822375172948804051847065 10366781379711603038885299)
              ·
                refine ⟨15550172069567404558327949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10366781379711603038885299 15550172069567404558327949)
                ·
                  refine ⟨5831314526087776709372981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15550172069567404558327949 5831314526087776709372981)
                  ·
                    refine ⟨546685736820729066503717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5831314526087776709372981 546685736820729066503717)
                    ·
                      refine ⟨102503575653886699969447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 546685736820729066503717 102503575653886699969447)
                      ·
                        rfl

theorem cell23_199625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_199625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199625 prefixEnd_199625 := by exact prefixLift 199625
  have htrace : WordTrace (prefixWord ++ tailWord_199625) baseStart_199625 baseEnd_199625 := by
    simpa [prefixWord, tailWord_199625, baseEnd_199625] using wordTrace_append hprefix tailTrace_199625
  have hstable : (prefixWord ++ tailWord_199625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199625).length < 2 ^ (prefixWord ++ tailWord_199625).sum := by decide
  have hdescent : baseEnd_199625 < baseStart_199625 := by decide
  rcases family_descends (prefixWord ++ tailWord_199625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199636 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_199636 : Nat := 118140960795 + 199636 * 2 ^ 59
def prefixEnd_199636 : Nat := 4983230072969 + 3 ^ 40 * 199636 * 2
def baseEnd_199636 : Nat := 102509223941086156931897

theorem tailTrace_199636 : CollatzResearch.WordTrace tailWord_199636 prefixEnd_199636 102509223941086156931897 := by
  unfold tailWord_199636
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640661552380170979729381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4854215403173561306305841 3640661552380170979729381)
  ·
    refine ⟨682624041071282058699259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3640661552380170979729381 682624041071282058699259)
    ·
      refine ⟨1023936061606923088048889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682624041071282058699259 1023936061606923088048889)
      ·
        refine ⟨767952046205192316036667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1023936061606923088048889 767952046205192316036667)
        ·
          refine ⟨1151928069307788474055001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767952046205192316036667 1151928069307788474055001)
          ·
            refine ⟨863946051980841355541251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1151928069307788474055001 863946051980841355541251)
            ·
              refine ⟨1295919077971262033311877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863946051980841355541251 1295919077971262033311877)
              ·
                refine ⟨242984827119611631245977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1295919077971262033311877 242984827119611631245977)
                ·
                  refine ⟨182238620339708723434483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242984827119611631245977 182238620339708723434483)
                  ·
                    refine ⟨273357930509563085151725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182238620339708723434483 273357930509563085151725)
                    ·
                      refine ⟨102509223941086156931897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 273357930509563085151725 102509223941086156931897)
                      ·
                        rfl

theorem cell23_199636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_199636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199636 prefixEnd_199636 := by exact prefixLift 199636
  have htrace : WordTrace (prefixWord ++ tailWord_199636) baseStart_199636 baseEnd_199636 := by
    simpa [prefixWord, tailWord_199636, baseEnd_199636] using wordTrace_append hprefix tailTrace_199636
  have hstable : (prefixWord ++ tailWord_199636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199636).length < 2 ^ (prefixWord ++ tailWord_199636).sum := by decide
  have hdescent : baseEnd_199636 < baseStart_199636 := by decide
  rcases family_descends (prefixWord ++ tailWord_199636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199637 : List Nat := [1, 3, 2, 3, 3, 2, 2, 2, 1, 2, 2]
def baseStart_199637 : Nat := 118140960795 + 199637 * 2 ^ 59
def prefixEnd_199637 : Nat := 4983230072969 + 3 ^ 40 * 199637 * 2
def baseEnd_199637 : Nat := 102509737421740653019393

theorem tailTrace_199637 : CollatzResearch.WordTrace tailWord_199637 prefixEnd_199637 102509737421740653019393 := by
  unfold tailWord_199637
  simp only [CollatzResearch.WordTrace]
  refine ⟨7281359577756719130245165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4854239718504479420163443 7281359577756719130245165)
  ·
    refine ⟨2730509841658769673841937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7281359577756719130245165 2730509841658769673841937)
    ·
      refine ⟨2047882381244077255381453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2730509841658769673841937 2047882381244077255381453)
      ·
        refine ⟨767955892966528970768045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2047882381244077255381453 767955892966528970768045)
        ·
          refine ⟨287983459862448364038017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767955892966528970768045 287983459862448364038017)
          ·
            refine ⟨215987594896836273028513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287983459862448364038017 215987594896836273028513)
            ·
              refine ⟨161990696172627204771385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215987594896836273028513 161990696172627204771385)
              ·
                refine ⟨121493022129470403578539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161990696172627204771385 121493022129470403578539)
                ·
                  refine ⟨182239533194205605367809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121493022129470403578539 182239533194205605367809)
                  ·
                    refine ⟨136679649895654204025857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 182239533194205605367809 136679649895654204025857)
                    ·
                      refine ⟨102509737421740653019393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136679649895654204025857 102509737421740653019393)
                      ·
                        rfl

theorem cell23_199637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_199637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199637 prefixEnd_199637 := by exact prefixLift 199637
  have htrace : WordTrace (prefixWord ++ tailWord_199637) baseStart_199637 baseEnd_199637 := by
    simpa [prefixWord, tailWord_199637, baseEnd_199637] using wordTrace_append hprefix tailTrace_199637
  have hstable : (prefixWord ++ tailWord_199637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199637).length < 2 ^ (prefixWord ++ tailWord_199637).sum := by decide
  have hdescent : baseEnd_199637 < baseStart_199637 := by decide
  rcases family_descends (prefixWord ++ tailWord_199637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199642 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_199642 : Nat := 118140960795 + 199642 * 2 ^ 59
def prefixEnd_199642 : Nat := 4983230072969 + 3 ^ 40 * 199642 * 2
def baseEnd_199642 : Nat := 102512304825013133456869

theorem tailTrace_199642 : CollatzResearch.WordTrace tailWord_199642 prefixEnd_199642 102512304825013133456869 := by
  unfold tailWord_199642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820385485684651246044295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4854361295159069989451453 1820385485684651246044295)
  ·
    refine ⟨2730578228526976869066443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1820385485684651246044295 2730578228526976869066443)
    ·
      refine ⟨4095867342790465303599665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2730578228526976869066443 4095867342790465303599665)
      ·
        refine ⟨3071900507092848977699749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4095867342790465303599665 3071900507092848977699749)
        ·
          refine ⟨575981345079909183318703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3071900507092848977699749 575981345079909183318703)
          ·
            refine ⟨863972017619863774978055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575981345079909183318703 863972017619863774978055)
            ·
              refine ⟨1295958026429795662467083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863972017619863774978055 1295958026429795662467083)
              ·
                refine ⟨1943937039644693493700625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295958026429795662467083 1943937039644693493700625)
                ·
                  refine ⟨1457952779733520120275469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1943937039644693493700625 1457952779733520120275469)
                  ·
                    refine ⟨546732292400070045103301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457952779733520120275469 546732292400070045103301)
                    ·
                      refine ⟨102512304825013133456869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 546732292400070045103301 102512304825013133456869)
                      ·
                        rfl

theorem cell23_199642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_199642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199642 prefixEnd_199642 := by exact prefixLift 199642
  have htrace : WordTrace (prefixWord ++ tailWord_199642) baseStart_199642 baseEnd_199642 := by
    simpa [prefixWord, tailWord_199642, baseEnd_199642] using wordTrace_append hprefix tailTrace_199642
  have hstable : (prefixWord ++ tailWord_199642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199642).length < 2 ^ (prefixWord ++ tailWord_199642).sum := by decide
  have hdescent : baseEnd_199642 < baseStart_199642 := by decide
  rcases family_descends (prefixWord ++ tailWord_199642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199659 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 8, 2, 2]
def baseStart_199659 : Nat := 118140960795 + 199659 * 2 ^ 59
def prefixEnd_199659 : Nat := 4983230072969 + 3 ^ 40 * 199659 * 2
def baseEnd_199659 : Nat := 102521033996139566944291

theorem tailTrace_199659 : CollatzResearch.WordTrace tailWord_199659 prefixEnd_199659 102521033996139566944291 := by
  unfold tailWord_199659
  simp only [CollatzResearch.WordTrace]
  refine ⟨7282161983677016887546031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4854774655784677925030687 7282161983677016887546031)
  ·
    refine ⟨10923242975515525331319047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7282161983677016887546031 10923242975515525331319047)
    ·
      refine ⟨16384864463273287996978571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10923242975515525331319047 16384864463273287996978571)
      ·
        refine ⟨24577296694909931995467857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16384864463273287996978571 24577296694909931995467857)
        ·
          refine ⟨18432972521182448996600893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24577296694909931995467857 18432972521182448996600893)
          ·
            refine ⟨6912364695443418373725335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18432972521182448996600893 6912364695443418373725335)
            ·
              refine ⟨10368547043165127560588003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6912364695443418373725335 10368547043165127560588003)
              ·
                refine ⟨15552820564747691340882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10368547043165127560588003 15552820564747691340882005)
                ·
                  refine ⟨182259615993137007900961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15552820564747691340882005 182259615993137007900961)
                  ·
                    refine ⟨136694711994852755925721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 182259615993137007900961 136694711994852755925721)
                    ·
                      refine ⟨102521033996139566944291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136694711994852755925721 102521033996139566944291)
                      ·
                        rfl

theorem cell23_199659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 2, 2].length) (baseStart_199659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199659 prefixEnd_199659 := by exact prefixLift 199659
  have htrace : WordTrace (prefixWord ++ tailWord_199659) baseStart_199659 baseEnd_199659 := by
    simpa [prefixWord, tailWord_199659, baseEnd_199659] using wordTrace_append hprefix tailTrace_199659
  have hstable : (prefixWord ++ tailWord_199659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199659).length < 2 ^ (prefixWord ++ tailWord_199659).sum := by decide
  have hdescent : baseEnd_199659 < baseStart_199659 := by decide
  rcases family_descends (prefixWord ++ tailWord_199659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199675 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 7]
def baseStart_199675 : Nat := 118140960795 + 199675 * 2 ^ 59
def prefixEnd_199675 : Nat := 4983230072969 + 3 ^ 40 * 199675 * 2
def baseEnd_199675 : Nat := 102529249686611504344217

theorem tailTrace_199675 : CollatzResearch.WordTrace tailWord_199675 prefixEnd_199675 102529249686611504344217 := by
  unfold tailWord_199675
  simp only [CollatzResearch.WordTrace]
  refine ⟨7282745551619051620128479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4855163701079367746752319 7282745551619051620128479)
  ·
    refine ⟨10924118327428577430192719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7282745551619051620128479 10924118327428577430192719)
    ·
      refine ⟨16386177491142866145289079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10924118327428577430192719 16386177491142866145289079)
      ·
        refine ⟨24579266236714299217933619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16386177491142866145289079 24579266236714299217933619)
        ·
          refine ⟨36868899355071448826900429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24579266236714299217933619 36868899355071448826900429)
          ·
            refine ⟨13825837258151793310087661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36868899355071448826900429 13825837258151793310087661)
            ·
              refine ⟨5184688971806922491282873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13825837258151793310087661 5184688971806922491282873)
              ·
                refine ⟨3888516728855191868462155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5184688971806922491282873 3888516728855191868462155)
                ·
                  refine ⟨5832775093282787802693233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888516728855191868462155 5832775093282787802693233)
                  ·
                    refine ⟨4374581319962090852019925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5832775093282787802693233 4374581319962090852019925)
                    ·
                      refine ⟨102529249686611504344217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4374581319962090852019925 102529249686611504344217)
                      ·
                        rfl

theorem cell23_199675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_199675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199675 prefixEnd_199675 := by exact prefixLift 199675
  have htrace : WordTrace (prefixWord ++ tailWord_199675) baseStart_199675 baseEnd_199675 := by
    simpa [prefixWord, tailWord_199675, baseEnd_199675] using wordTrace_append hprefix tailTrace_199675
  have hstable : (prefixWord ++ tailWord_199675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199675).length < 2 ^ (prefixWord ++ tailWord_199675).sum := by decide
  have hdescent : baseEnd_199675 < baseStart_199675 := by decide
  rcases family_descends (prefixWord ++ tailWord_199675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199695 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 11]
def baseStart_199695 : Nat := 118140960795 + 199695 * 2 ^ 59
def prefixEnd_199695 : Nat := 4983230072969 + 3 ^ 40 * 199695 * 2
def baseEnd_199695 : Nat := 34179839766567142031375

theorem tailTrace_199695 : CollatzResearch.WordTrace tailWord_199695 prefixEnd_199695 34179839766567142031375 := by
  unfold tailWord_199695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7283475011546595035856539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4855650007697730023904359 7283475011546595035856539)
  ·
    refine ⟨10925212517319892553784809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7283475011546595035856539 10925212517319892553784809)
    ·
      refine ⟨8193909387989919415338607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10925212517319892553784809 8193909387989919415338607)
      ·
        refine ⟨12290864081984879123007911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8193909387989919415338607 12290864081984879123007911)
        ·
          refine ⟨18436296122977318684511867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12290864081984879123007911 18436296122977318684511867)
          ·
            refine ⟨27654444184465978026767801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18436296122977318684511867 27654444184465978026767801)
            ·
              refine ⟨20740833138349483520075851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27654444184465978026767801 20740833138349483520075851)
              ·
                refine ⟨31111249707524225280113777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20740833138349483520075851 31111249707524225280113777)
                ·
                  refine ⟨23333437280643168960085333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31111249707524225280113777 23333437280643168960085333)
                  ·
                    refine ⟨34179839766567142031375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 23333437280643168960085333 34179839766567142031375)
                    ·
                      rfl

theorem cell23_199695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_199695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199695 prefixEnd_199695 := by exact prefixLift 199695
  have htrace : WordTrace (prefixWord ++ tailWord_199695) baseStart_199695 baseEnd_199695 := by
    simpa [prefixWord, tailWord_199695, baseEnd_199695] using wordTrace_append hprefix tailTrace_199695
  have hstable : (prefixWord ++ tailWord_199695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199695).length < 2 ^ (prefixWord ++ tailWord_199695).sum := by decide
  have hdescent : baseEnd_199695 < baseStart_199695 := by decide
  rcases family_descends (prefixWord ++ tailWord_199695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199749 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 4, 4, 2]
def baseStart_199749 : Nat := 118140960795 + 199749 * 2 ^ 59
def prefixEnd_199749 : Nat := 4983230072969 + 3 ^ 40 * 199749 * 2
def baseEnd_199749 : Nat := 102567247255044214818877

theorem tailTrace_199749 : CollatzResearch.WordTrace tailWord_199749 prefixEnd_199749 102567247255044214818877 := by
  unfold tailWord_199749
  simp only [CollatzResearch.WordTrace]
  refine ⟨7285444553350962258322301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4856963035567308172214867 7285444553350962258322301)
  ·
    refine ⟨2732041707506610846870863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7285444553350962258322301 2732041707506610846870863)
    ·
      refine ⟨4098062561259916270306295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2732041707506610846870863 4098062561259916270306295)
      ·
        refine ⟨6147093841889874405459443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098062561259916270306295 6147093841889874405459443)
        ·
          refine ⟨9220640762834811608189165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6147093841889874405459443 9220640762834811608189165)
          ·
            refine ⟨3457740286063054353070937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9220640762834811608189165 3457740286063054353070937)
            ·
              refine ⟨2593305214547290764803203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3457740286063054353070937 2593305214547290764803203)
              ·
                refine ⟨3889957821820936147204805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593305214547290764803203 3889957821820936147204805)
                ·
                  refine ⟨729367091591425527600901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3889957821820936147204805 729367091591425527600901)
                  ·
                    refine ⟨136756329673392286425169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 729367091591425527600901 136756329673392286425169)
                    ·
                      refine ⟨102567247255044214818877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136756329673392286425169 102567247255044214818877)
                      ·
                        rfl

theorem cell23_199749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_199749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199749 prefixEnd_199749 := by exact prefixLift 199749
  have htrace : WordTrace (prefixWord ++ tailWord_199749) baseStart_199749 baseEnd_199749 := by
    simpa [prefixWord, tailWord_199749, baseEnd_199749] using wordTrace_append hprefix tailTrace_199749
  have hstable : (prefixWord ++ tailWord_199749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199749).length < 2 ^ (prefixWord ++ tailWord_199749).sum := by decide
  have hdescent : baseEnd_199749 < baseStart_199749 := by decide
  rcases family_descends (prefixWord ++ tailWord_199749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199750 : List Nat := [6, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_199750 : Nat := 118140960795 + 199750 * 2 ^ 59
def prefixEnd_199750 : Nat := 4983230072969 + 3 ^ 40 * 199750 * 2
def baseEnd_199750 : Nat := 11396417859522078989597

theorem tailTrace_199750 : CollatzResearch.WordTrace tailWord_199750 prefixEnd_199750 11396417859522078989597 := by
  unfold tailWord_199750
  simp only [CollatzResearch.WordTrace]
  refine ⟨227671282073354357159647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4856987350898226286072469 227671282073354357159647)
  ·
    refine ⟨341506923110031535739471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227671282073354357159647 341506923110031535739471)
    ·
      refine ⟨512260384665047303609207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341506923110031535739471 512260384665047303609207)
      ·
        refine ⟨768390576997570955413811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512260384665047303609207 768390576997570955413811)
        ·
          refine ⟨1152585865496356433120717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768390576997570955413811 1152585865496356433120717)
          ·
            refine ⟨432219699561133662420269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1152585865496356433120717 432219699561133662420269)
            ·
              refine ⟨162082387335425123407601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432219699561133662420269 162082387335425123407601)
              ·
                refine ⟨121561790501568842555701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162082387335425123407601 121561790501568842555701)
                ·
                  refine ⟨11396417859522078989597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121561790501568842555701 11396417859522078989597)
                  ·
                    rfl

theorem cell23_199750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_199750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199750 prefixEnd_199750 := by exact prefixLift 199750
  have htrace : WordTrace (prefixWord ++ tailWord_199750) baseStart_199750 baseEnd_199750 := by
    simpa [prefixWord, tailWord_199750, baseEnd_199750] using wordTrace_append hprefix tailTrace_199750
  have hstable : (prefixWord ++ tailWord_199750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199750).length < 2 ^ (prefixWord ++ tailWord_199750).sum := by decide
  have hdescent : baseEnd_199750 < baseStart_199750 := by decide
  rcases family_descends (prefixWord ++ tailWord_199750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199786 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_199786 : Nat := 118140960795 + 199786 * 2 ^ 59
def prefixEnd_199786 : Nat := 4983230072969 + 3 ^ 40 * 199786 * 2
def baseEnd_199786 : Nat := 102586246039260570056207

theorem tailTrace_199786 : CollatzResearch.WordTrace tailWord_199786 prefixEnd_199786 102586246039260570056207 := by
  unfold tailWord_199786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821698513554229394354803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4857862702811278384946141 1821698513554229394354803)
  ·
    refine ⟨2732547770331344091532205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1821698513554229394354803 2732547770331344091532205)
    ·
      refine ⟨1024705413874254034324577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2732547770331344091532205 1024705413874254034324577)
      ·
        refine ⟨768529060405690525743433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024705413874254034324577 768529060405690525743433)
        ·
          refine ⟨576396795304267894307575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768529060405690525743433 576396795304267894307575)
          ·
            refine ⟨864595192956401841461363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576396795304267894307575 864595192956401841461363)
            ·
              refine ⟨1296892789434602762192045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864595192956401841461363 1296892789434602762192045)
              ·
                refine ⟨486334796037976035822017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1296892789434602762192045 486334796037976035822017)
                ·
                  refine ⟨364751097028482026866513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486334796037976035822017 364751097028482026866513)
                  ·
                    refine ⟨273563322771361520149885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 364751097028482026866513 273563322771361520149885)
                    ·
                      refine ⟨102586246039260570056207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 273563322771361520149885 102586246039260570056207)
                      ·
                        rfl

theorem cell23_199786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_199786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199786 prefixEnd_199786 := by exact prefixLift 199786
  have htrace : WordTrace (prefixWord ++ tailWord_199786) baseStart_199786 baseEnd_199786 := by
    simpa [prefixWord, tailWord_199786, baseEnd_199786] using wordTrace_append hprefix tailTrace_199786
  have hstable : (prefixWord ++ tailWord_199786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199786).length < 2 ^ (prefixWord ++ tailWord_199786).sum := by decide
  have hdescent : baseEnd_199786 < baseStart_199786 := by decide
  rcases family_descends (prefixWord ++ tailWord_199786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199853 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_199853 : Nat := 118140960795 + 199853 * 2 ^ 59
def prefixEnd_199853 : Nat := 4983230072969 + 3 ^ 40 * 199853 * 2
def baseEnd_199853 : Nat := 34206883081037269306133

theorem tailTrace_199853 : CollatzResearch.WordTrace tailWord_199853 prefixEnd_199853 34206883081037269306133 := by
  unfold tailWord_199853
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289237744974188020108213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4859491829982792013405475 7289237744974188020108213)
  ·
    refine ⟨683366038591330126885145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7289237744974188020108213 683366038591330126885145)
    ·
      refine ⟨512524528943497595163859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 683366038591330126885145 512524528943497595163859)
      ·
        refine ⟨768786793415246392745789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512524528943497595163859 768786793415246392745789)
        ·
          refine ⟨288295047530717397279671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 768786793415246392745789 288295047530717397279671)
          ·
            refine ⟨432442571296076095919507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288295047530717397279671 432442571296076095919507)
            ·
              refine ⟨648663856944114143879261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432442571296076095919507 648663856944114143879261)
              ·
                refine ⟨243248946354042803954723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648663856944114143879261 243248946354042803954723)
                ·
                  refine ⟨364873419531064205932085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243248946354042803954723 364873419531064205932085)
                  ·
                    refine ⟨34206883081037269306133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 364873419531064205932085 34206883081037269306133)
                    ·
                      rfl

theorem cell23_199853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_199853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199853 prefixEnd_199853 := by exact prefixLift 199853
  have htrace : WordTrace (prefixWord ++ tailWord_199853) baseStart_199853 baseEnd_199853 := by
    simpa [prefixWord, tailWord_199853, baseEnd_199853] using wordTrace_append hprefix tailTrace_199853
  have hstable : (prefixWord ++ tailWord_199853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199853).length < 2 ^ (prefixWord ++ tailWord_199853).sum := by decide
  have hdescent : baseEnd_199853 < baseStart_199853 := by decide
  rcases family_descends (prefixWord ++ tailWord_199853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199869 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_199869 : Nat := 118140960795 + 199869 * 2 ^ 59
def prefixEnd_199869 : Nat := 4983230072969 + 3 ^ 40 * 199869 * 2
def baseEnd_199869 : Nat := 102628864933583745318325

theorem tailTrace_199869 : CollatzResearch.WordTrace tailWord_199869 prefixEnd_199869 102628864933583745318325 := by
  unfold tailWord_199869
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289821312916222752690661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4859880875277481835127107 7289821312916222752690661)
  ·
    refine ⟨1366841496171791766129499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7289821312916222752690661 1366841496171791766129499)
    ·
      refine ⟨2050262244257687649194249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366841496171791766129499 2050262244257687649194249)
      ·
        refine ⟨1537696683193265736895687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2050262244257687649194249 1537696683193265736895687)
        ·
          refine ⟨2306545024789898605343531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537696683193265736895687 2306545024789898605343531)
          ·
            refine ⟨3459817537184847908015297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306545024789898605343531 3459817537184847908015297)
            ·
              refine ⟨2594863152888635931011473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459817537184847908015297 2594863152888635931011473)
              ·
                refine ⟨1946147364666476948258605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2594863152888635931011473 1946147364666476948258605)
                ·
                  refine ⟨729805261749928855596977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1946147364666476948258605 729805261749928855596977)
                  ·
                    refine ⟨547353946312446641697733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 729805261749928855596977 547353946312446641697733)
                    ·
                      refine ⟨102628864933583745318325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 547353946312446641697733 102628864933583745318325)
                      ·
                        rfl

theorem cell23_199869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_199869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199869 prefixEnd_199869 := by exact prefixLift 199869
  have htrace : WordTrace (prefixWord ++ tailWord_199869) baseStart_199869 baseEnd_199869 := by
    simpa [prefixWord, tailWord_199869, baseEnd_199869] using wordTrace_append hprefix tailTrace_199869
  have hstable : (prefixWord ++ tailWord_199869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199869).length < 2 ^ (prefixWord ++ tailWord_199869).sum := by decide
  have hdescent : baseEnd_199869 < baseStart_199869 := by decide
  rcases family_descends (prefixWord ++ tailWord_199869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199886 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_199886 : Nat := 118140960795 + 199886 * 2 ^ 59
def prefixEnd_199886 : Nat := 4983230072969 + 3 ^ 40 * 199886 * 2
def baseEnd_199886 : Nat := 102637594104710178805747

theorem tailTrace_199886 : CollatzResearch.WordTrace tailWord_199886 prefixEnd_199886 102637594104710178805747 := by
  unfold tailWord_199886
  simp only [CollatzResearch.WordTrace]
  refine ⟨911305169231829332007439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4860294235903089770706341 911305169231829332007439)
  ·
    refine ⟨1366957753847743998011159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 911305169231829332007439 1366957753847743998011159)
    ·
      refine ⟨2050436630771615997016739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366957753847743998011159 2050436630771615997016739)
      ·
        refine ⟨3075654946157423995525109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050436630771615997016739 3075654946157423995525109)
        ·
          refine ⟨288342651202258499580479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3075654946157423995525109 288342651202258499580479)
          ·
            refine ⟨432513976803387749370719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288342651202258499580479 432513976803387749370719)
            ·
              refine ⟨648770965205081624056079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432513976803387749370719 648770965205081624056079)
              ·
                refine ⟨973156447807622436084119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648770965205081624056079 973156447807622436084119)
                ·
                  refine ⟨1459734671711433654126179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973156447807622436084119 1459734671711433654126179)
                  ·
                    refine ⟨2189602007567150481189269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1459734671711433654126179 2189602007567150481189269)
                    ·
                      refine ⟨102637594104710178805747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2189602007567150481189269 102637594104710178805747)
                      ·
                        rfl

theorem cell23_199886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_199886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199886 prefixEnd_199886 := by exact prefixLift 199886
  have htrace : WordTrace (prefixWord ++ tailWord_199886) baseStart_199886 baseEnd_199886 := by
    simpa [prefixWord, tailWord_199886, baseEnd_199886] using wordTrace_append hprefix tailTrace_199886
  have hstable : (prefixWord ++ tailWord_199886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199886).length < 2 ^ (prefixWord ++ tailWord_199886).sum := by decide
  have hdescent : baseEnd_199886 < baseStart_199886 := by decide
  rcases family_descends (prefixWord ++ tailWord_199886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199893 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_199893 : Nat := 118140960795 + 199893 * 2 ^ 59
def prefixEnd_199893 : Nat := 4983230072969 + 3 ^ 40 * 199893 * 2
def baseEnd_199893 : Nat := 102641188469291651418215

theorem tailTrace_199893 : CollatzResearch.WordTrace tailWord_199893 prefixEnd_199893 102641188469291651418215 := by
  unfold tailWord_199893
  simp only [CollatzResearch.WordTrace]
  refine ⟨7290696664829274851564333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4860464443219516567709555 7290696664829274851564333)
  ·
    refine ⟨2734011249310978069336625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7290696664829274851564333 2734011249310978069336625)
    ·
      refine ⟨2050508436983233552002469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2734011249310978069336625 2050508436983233552002469)
      ·
        refine ⟨384470331934356291000463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2050508436983233552002469 384470331934356291000463)
        ·
          refine ⟨576705497901534436500695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384470331934356291000463 576705497901534436500695)
          ·
            refine ⟨865058246852301654751043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576705497901534436500695 865058246852301654751043)
            ·
              refine ⟨1297587370278452482126565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865058246852301654751043 1297587370278452482126565)
              ·
                refine ⟨243297631927209840398731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1297587370278452482126565 243297631927209840398731)
                ·
                  refine ⟨364946447890814760598097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243297631927209840398731 364946447890814760598097)
                  ·
                    refine ⟨273709835918111070448573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 364946447890814760598097 273709835918111070448573)
                    ·
                      refine ⟨102641188469291651418215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 273709835918111070448573 102641188469291651418215)
                      ·
                        rfl

theorem cell23_199893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_199893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199893 prefixEnd_199893 := by exact prefixLift 199893
  have htrace : WordTrace (prefixWord ++ tailWord_199893) baseStart_199893 baseEnd_199893 := by
    simpa [prefixWord, tailWord_199893, baseEnd_199893] using wordTrace_append hprefix tailTrace_199893
  have hstable : (prefixWord ++ tailWord_199893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199893).length < 2 ^ (prefixWord ++ tailWord_199893).sum := by decide
  have hdescent : baseEnd_199893 < baseStart_199893 := by decide
  rcases family_descends (prefixWord ++ tailWord_199893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199929 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_199929 : Nat := 118140960795 + 199929 * 2 ^ 59
def prefixEnd_199929 : Nat := 4983230072969 + 3 ^ 40 * 199929 * 2
def baseEnd_199929 : Nat := 102659673772853510568049

theorem tailTrace_199929 : CollatzResearch.WordTrace tailWord_199929 prefixEnd_199929 102659673772853510568049 := by
  unfold tailWord_199929
  simp only [CollatzResearch.WordTrace]
  refine ⟨7292009692698852999874841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4861339795132568666583227 7292009692698852999874841)
  ·
    refine ⟨5469007269524139749906131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7292009692698852999874841 5469007269524139749906131)
    ·
      refine ⟨8203510904286209624859197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5469007269524139749906131 8203510904286209624859197)
      ·
        refine ⟨3076316589107328609322199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8203510904286209624859197 3076316589107328609322199)
        ·
          refine ⟨4614474883660992913983299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076316589107328609322199 4614474883660992913983299)
          ·
            refine ⟨6921712325491489370974949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614474883660992913983299 6921712325491489370974949)
            ·
              refine ⟨1297821061029654257057803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6921712325491489370974949 1297821061029654257057803)
              ·
                refine ⟨1946731591544481385586705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297821061029654257057803 1946731591544481385586705)
                ·
                  refine ⟨1460048693658361039190029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1946731591544481385586705 1460048693658361039190029)
                  ·
                    refine ⟨547518260121885389696261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1460048693658361039190029 547518260121885389696261)
                    ·
                      refine ⟨102659673772853510568049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 547518260121885389696261 102659673772853510568049)
                      ·
                        rfl

theorem cell23_199929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_199929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199929 prefixEnd_199929 := by exact prefixLift 199929
  have htrace : WordTrace (prefixWord ++ tailWord_199929) baseStart_199929 baseEnd_199929 := by
    simpa [prefixWord, tailWord_199929, baseEnd_199929] using wordTrace_append hprefix tailTrace_199929
  have hstable : (prefixWord ++ tailWord_199929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199929).length < 2 ^ (prefixWord ++ tailWord_199929).sum := by decide
  have hdescent : baseEnd_199929 < baseStart_199929 := by decide
  rcases family_descends (prefixWord ++ tailWord_199929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199940 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_199940 : Nat := 118140960795 + 199940 * 2 ^ 59
def prefixEnd_199940 : Nat := 4983230072969 + 3 ^ 40 * 199940 * 2
def baseEnd_199940 : Nat := 102665322060052967530499

theorem tailTrace_199940 : CollatzResearch.WordTrace tailWord_199940 prefixEnd_199940 102665322060052967530499 := by
  unfold tailWord_199940
  simp only [CollatzResearch.WordTrace]
  refine ⟨3646205447829500939262637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4861607263772667919016849 3646205447829500939262637)
  ·
    refine ⟨1367327042936062852223489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3646205447829500939262637 1367327042936062852223489)
    ·
      refine ⟨1025495282202047139167617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1367327042936062852223489 1025495282202047139167617)
      ·
        refine ⟨769121461651535354375713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1025495282202047139167617 769121461651535354375713)
        ·
          refine ⟨576841096238651515781785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769121461651535354375713 576841096238651515781785)
          ·
            refine ⟨432630822178988636836339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576841096238651515781785 432630822178988636836339)
            ·
              refine ⟨648946233268482955254509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432630822178988636836339 648946233268482955254509)
              ·
                refine ⟨243354837475681108220441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648946233268482955254509 243354837475681108220441)
                ·
                  refine ⟨182516128106760831165331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243354837475681108220441 182516128106760831165331)
                  ·
                    refine ⟨273774192160141246747997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182516128106760831165331 273774192160141246747997)
                    ·
                      refine ⟨102665322060052967530499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 273774192160141246747997 102665322060052967530499)
                      ·
                        rfl

theorem cell23_199940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_199940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199940 prefixEnd_199940 := by exact prefixLift 199940
  have htrace : WordTrace (prefixWord ++ tailWord_199940) baseStart_199940 baseEnd_199940 := by
    simpa [prefixWord, tailWord_199940, baseEnd_199940] using wordTrace_append hprefix tailTrace_199940
  have hstable : (prefixWord ++ tailWord_199940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199940).length < 2 ^ (prefixWord ++ tailWord_199940).sum := by decide
  have hdescent : baseEnd_199940 < baseStart_199940 := by decide
  rcases family_descends (prefixWord ++ tailWord_199940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199950 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_199950 : Nat := 118140960795 + 199950 * 2 ^ 59
def prefixEnd_199950 : Nat := 4983230072969 + 3 ^ 40 * 199950 * 2
def baseEnd_199950 : Nat := 102670456866597928405453

theorem tailTrace_199950 : CollatzResearch.WordTrace tailWord_199950 prefixEnd_199950 102670456866597928405453 := by
  unfold tailWord_199950
  simp only [CollatzResearch.WordTrace]
  refine ⟨911596953202846698298663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4861850417081849057592869 911596953202846698298663)
  ·
    refine ⟨1367395429804270047447995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 911596953202846698298663 1367395429804270047447995)
    ·
      refine ⟨2051093144706405071171993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1367395429804270047447995 2051093144706405071171993)
      ·
        refine ⟨1538319858529803803378995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2051093144706405071171993 1538319858529803803378995)
        ·
          refine ⟨2307479787794705705068493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538319858529803803378995 2307479787794705705068493)
          ·
            refine ⟨865304920423014639400685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2307479787794705705068493 865304920423014639400685)
            ·
              refine ⟨324489345158630489775257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 865304920423014639400685 324489345158630489775257)
              ·
                refine ⟨243367008868972867331443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324489345158630489775257 243367008868972867331443)
                ·
                  refine ⟨365050513303459300997165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243367008868972867331443 365050513303459300997165)
                  ·
                    refine ⟨136893942488797237873937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365050513303459300997165 136893942488797237873937)
                    ·
                      refine ⟨102670456866597928405453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136893942488797237873937 102670456866597928405453)
                      ·
                        rfl

theorem cell23_199950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_199950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199950 prefixEnd_199950 := by exact prefixLift 199950
  have htrace : WordTrace (prefixWord ++ tailWord_199950) baseStart_199950 baseEnd_199950 := by
    simpa [prefixWord, tailWord_199950, baseEnd_199950] using wordTrace_append hprefix tailTrace_199950
  have hstable : (prefixWord ++ tailWord_199950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199950).length < 2 ^ (prefixWord ++ tailWord_199950).sum := by decide
  have hdescent : baseEnd_199950 < baseStart_199950 := by decide
  rcases family_descends (prefixWord ++ tailWord_199950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199967 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 1, 3, 2]
def baseStart_199967 : Nat := 118140960795 + 199967 * 2 ^ 59
def prefixEnd_199967 : Nat := 4983230072969 + 3 ^ 40 * 199967 * 2
def baseEnd_199967 : Nat := 102679186037724361892875

theorem tailTrace_199967 : CollatzResearch.WordTrace tailWord_199967 prefixEnd_199967 102679186037724361892875 := by
  unfold tailWord_199967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7293395666561185489758155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4862263777707456993172103 7293395666561185489758155)
  ·
    refine ⟨10940093499841778234637233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7293395666561185489758155 10940093499841778234637233)
    ·
      refine ⟨8205070124881333675977925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10940093499841778234637233 8205070124881333675977925)
      ·
        refine ⟨1538450648415250064245861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8205070124881333675977925 1538450648415250064245861)
        ·
          refine ⟨288459496577859387046099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1538450648415250064245861 288459496577859387046099)
          ·
            refine ⟨432689244866789080569149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288459496577859387046099 432689244866789080569149)
            ·
              refine ⟨162258466825045905213431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432689244866789080569149 162258466825045905213431)
              ·
                refine ⟨243387700237568857820147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162258466825045905213431 243387700237568857820147)
                ·
                  refine ⟨365081550356353286730221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243387700237568857820147 365081550356353286730221)
                  ·
                    refine ⟨136905581383632482523833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365081550356353286730221 136905581383632482523833)
                    ·
                      refine ⟨102679186037724361892875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136905581383632482523833 102679186037724361892875)
                      ·
                        rfl

theorem cell23_199967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_199967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199967 prefixEnd_199967 := by exact prefixLift 199967
  have htrace : WordTrace (prefixWord ++ tailWord_199967) baseStart_199967 baseEnd_199967 := by
    simpa [prefixWord, tailWord_199967, baseEnd_199967] using wordTrace_append hprefix tailTrace_199967
  have hstable : (prefixWord ++ tailWord_199967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199967).length < 2 ^ (prefixWord ++ tailWord_199967).sum := by decide
  have hdescent : baseEnd_199967 < baseStart_199967 := by decide
  rcases family_descends (prefixWord ++ tailWord_199967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199990 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_199990 : Nat := 118140960795 + 199990 * 2 ^ 59
def prefixEnd_199990 : Nat := 4983230072969 + 3 ^ 40 * 199990 * 2
def baseEnd_199990 : Nat := 34230332030925923968423

theorem tailTrace_199990 : CollatzResearch.WordTrace tailWord_199990 prefixEnd_199990 34230332030925923968423 := by
  unfold tailWord_199990
  simp only [CollatzResearch.WordTrace]
  refine ⟨455889659092366276115339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4862823030318573611896949 455889659092366276115339)
  ·
    refine ⟨683834488638549414173009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 455889659092366276115339 683834488638549414173009)
    ·
      refine ⟨512875866478912060629757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 683834488638549414173009 512875866478912060629757)
      ·
        refine ⟨192328449929592022736159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 512875866478912060629757 192328449929592022736159)
        ·
          refine ⟨288492674894388034104239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192328449929592022736159 288492674894388034104239)
          ·
            refine ⟨432739012341582051156359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288492674894388034104239 432739012341582051156359)
            ·
              refine ⟨649108518512373076734539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432739012341582051156359 649108518512373076734539)
              ·
                refine ⟨973662777768559615101809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649108518512373076734539 973662777768559615101809)
                ·
                  refine ⟨730247083326419711326357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 973662777768559615101809 730247083326419711326357)
                  ·
                    refine ⟨34230332030925923968423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 730247083326419711326357 34230332030925923968423)
                    ·
                      rfl

theorem cell23_199990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_199990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199990 prefixEnd_199990 := by exact prefixLift 199990
  have htrace : WordTrace (prefixWord ++ tailWord_199990) baseStart_199990 baseEnd_199990 := by
    simpa [prefixWord, tailWord_199990, baseEnd_199990] using wordTrace_append hprefix tailTrace_199990
  have hstable : (prefixWord ++ tailWord_199990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199990).length < 2 ^ (prefixWord ++ tailWord_199990).sum := by decide
  have hdescent : baseEnd_199990 < baseStart_199990 := by decide
  rcases family_descends (prefixWord ++ tailWord_199990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199993 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 4]
def baseStart_199993 : Nat := 118140960795 + 199993 * 2 ^ 59
def prefixEnd_199993 : Nat := 4983230072969 + 3 ^ 40 * 199993 * 2
def baseEnd_199993 : Nat := 102692536534741260167755

theorem tailTrace_199993 : CollatzResearch.WordTrace tailWord_199993 prefixEnd_199993 102692536534741260167755 := by
  unfold tailWord_199993
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294343964466991930204633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4862895976311327953469755 7294343964466991930204633)
  ·
    refine ⟨5470757973350243947653475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7294343964466991930204633 5470757973350243947653475)
    ·
      refine ⟨8206136960025365921480213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5470757973350243947653475 8206136960025365921480213)
      ·
        refine ⟨384662670001189027569385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8206136960025365921480213 384662670001189027569385)
        ·
          refine ⟨288497002500891770677039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384662670001189027569385 288497002500891770677039)
          ·
            refine ⟨432745503751337656015559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288497002500891770677039 432745503751337656015559)
            ·
              refine ⟨649118255627006484023339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432745503751337656015559 649118255627006484023339)
              ·
                refine ⟨973677383440509726035009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649118255627006484023339 973677383440509726035009)
                ·
                  refine ⟨730258037580382294526257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 973677383440509726035009 730258037580382294526257)
                  ·
                    refine ⟨547693528185286720894693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 730258037580382294526257 547693528185286720894693)
                    ·
                      refine ⟨102692536534741260167755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 547693528185286720894693 102692536534741260167755)
                      ·
                        rfl

theorem cell23_199993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_199993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199993 prefixEnd_199993 := by exact prefixLift 199993
  have htrace : WordTrace (prefixWord ++ tailWord_199993) baseStart_199993 baseEnd_199993 := by
    simpa [prefixWord, tailWord_199993, baseEnd_199993] using wordTrace_append hprefix tailTrace_199993
  have hstable : (prefixWord ++ tailWord_199993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199993).length < 2 ^ (prefixWord ++ tailWord_199993).sum := by decide
  have hdescent : baseEnd_199993 < baseStart_199993 := by decide
  rcases family_descends (prefixWord ++ tailWord_199993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199996 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_199996 : Nat := 118140960795 + 199996 * 2 ^ 59
def prefixEnd_199996 : Nat := 4983230072969 + 3 ^ 40 * 199996 * 2
def baseEnd_199996 : Nat := 102694076976704748430241

theorem tailTrace_199996 : CollatzResearch.WordTrace tailWord_199996 prefixEnd_199996 102694076976704748430241 := by
  unfold tailWord_199996
  simp only [CollatzResearch.WordTrace]
  refine ⟨3647226691728061721281921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4862968922304082295042561 3647226691728061721281921)
  ·
    refine ⟨2735420018796046290961441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3647226691728061721281921 2735420018796046290961441)
    ·
      refine ⟨2051565014097034718221081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2735420018796046290961441 2051565014097034718221081)
      ·
        refine ⟨1538673760572776038665811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2051565014097034718221081 1538673760572776038665811)
        ·
          refine ⟨2308010640859164057998717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538673760572776038665811 2308010640859164057998717)
          ·
            refine ⟨865503990322186521749519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2308010640859164057998717 865503990322186521749519)
            ·
              refine ⟨1298255985483279782624279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865503990322186521749519 1298255985483279782624279)
              ·
                refine ⟨1947383978224919673936419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298255985483279782624279 1947383978224919673936419)
                ·
                  refine ⟨2921075967337379510904629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947383978224919673936419 2921075967337379510904629)
                  ·
                    refine ⟨273850871937879329147309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2921075967337379510904629 273850871937879329147309)
                    ·
                      refine ⟨102694076976704748430241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 273850871937879329147309 102694076976704748430241)
                      ·
                        rfl

theorem cell23_199996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_199996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199996 prefixEnd_199996 := by exact prefixLift 199996
  have htrace : WordTrace (prefixWord ++ tailWord_199996) baseStart_199996 baseEnd_199996 := by
    simpa [prefixWord, tailWord_199996, baseEnd_199996] using wordTrace_append hprefix tailTrace_199996
  have hstable : (prefixWord ++ tailWord_199996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199996).length < 2 ^ (prefixWord ++ tailWord_199996).sum := by decide
  have hdescent : baseEnd_199996 < baseStart_199996 := by decide
  rcases family_descends (prefixWord ++ tailWord_199996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199997 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_199997 : Nat := 118140960795 + 199997 * 2 ^ 59
def prefixEnd_199997 : Nat := 4983230072969 + 3 ^ 40 * 199997 * 2
def baseEnd_199997 : Nat := 102694590457359244517737

theorem tailTrace_199997 : CollatzResearch.WordTrace tailWord_199997 prefixEnd_199997 102694590457359244517737 := by
  unfold tailWord_199997
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294489856452500613350245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4862993237635000408900163 7294489856452500613350245)
  ·
    refine ⟨1367716848084843865003171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7294489856452500613350245 1367716848084843865003171)
    ·
      refine ⟨2051575272127265797504757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1367716848084843865003171 2051575272127265797504757)
      ·
        refine ⟨192335181761931168516071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2051575272127265797504757 192335181761931168516071)
        ·
          refine ⟨288502772642896752774107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192335181761931168516071 288502772642896752774107)
          ·
            refine ⟨432754158964345129161161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288502772642896752774107 432754158964345129161161)
            ·
              refine ⟨324565619223258846870871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432754158964345129161161 324565619223258846870871)
              ·
                refine ⟨486848428834888270306307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324565619223258846870871 486848428834888270306307)
                ·
                  refine ⟨730272643252332405459461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486848428834888270306307 730272643252332405459461)
                  ·
                    refine ⟨136926120609812326023649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730272643252332405459461 136926120609812326023649)
                    ·
                      refine ⟨102694590457359244517737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 136926120609812326023649 102694590457359244517737)
                      ·
                        rfl

theorem cell23_199997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_199997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_199997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_199997 prefixEnd_199997 := by exact prefixLift 199997
  have htrace : WordTrace (prefixWord ++ tailWord_199997) baseStart_199997 baseEnd_199997 := by
    simpa [prefixWord, tailWord_199997, baseEnd_199997] using wordTrace_append hprefix tailTrace_199997
  have hstable : (prefixWord ++ tailWord_199997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199997).length < 2 ^ (prefixWord ++ tailWord_199997).sum := by decide
  have hdescent : baseEnd_199997 < baseStart_199997 := by decide
  rcases family_descends (prefixWord ++ tailWord_199997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200009 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_200009 : Nat := 118140960795 + 200009 * 2 ^ 59
def prefixEnd_200009 : Nat := 4983230072969 + 3 ^ 40 * 200009 * 2
def baseEnd_200009 : Nat := 102700752225213197567681

theorem tailTrace_200009 : CollatzResearch.WordTrace tailWord_200009 prefixEnd_200009 102700752225213197567681 := by
  unfold tailWord_200009
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294927532409026662787081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4863285021606017775191387 7294927532409026662787081)
  ·
    refine ⟨5471195649306769997090311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7294927532409026662787081 5471195649306769997090311)
    ·
      refine ⟨8206793473960154995635467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5471195649306769997090311 8206793473960154995635467)
      ·
        refine ⟨12310190210940232493453201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8206793473960154995635467 12310190210940232493453201)
        ·
          refine ⟨9232642658205174370089901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12310190210940232493453201 9232642658205174370089901)
          ·
            refine ⟨3462240996826940388783713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9232642658205174370089901 3462240996826940388783713)
            ·
              refine ⟨2596680747620205291587785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462240996826940388783713 2596680747620205291587785)
              ·
                refine ⟨1947510560715153968690839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596680747620205291587785 1947510560715153968690839)
                ·
                  refine ⟨2921265841072730953036259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947510560715153968690839 2921265841072730953036259)
                  ·
                    refine ⟨4381898761609096429554389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921265841072730953036259 4381898761609096429554389)
                    ·
                      refine ⟨102700752225213197567681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4381898761609096429554389 102700752225213197567681)
                      ·
                        rfl

theorem cell23_200009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_200009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200009 prefixEnd_200009 := by exact prefixLift 200009
  have htrace : WordTrace (prefixWord ++ tailWord_200009) baseStart_200009 baseEnd_200009 := by
    simpa [prefixWord, tailWord_200009, baseEnd_200009] using wordTrace_append hprefix tailTrace_200009
  have hstable : (prefixWord ++ tailWord_200009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200009).length < 2 ^ (prefixWord ++ tailWord_200009).sum := by decide
  have hdescent : baseEnd_200009 < baseStart_200009 := by decide
  rcases family_descends (prefixWord ++ tailWord_200009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200143 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 4]
def baseStart_200143 : Nat := 118140960795 + 200143 * 2 ^ 59
def prefixEnd_200143 : Nat := 4983230072969 + 3 ^ 40 * 200143 * 2
def baseEnd_200143 : Nat := 102769558632915673292065

theorem tailTrace_200143 : CollatzResearch.WordTrace tailWord_200143 prefixEnd_200143 102769558632915673292065 := by
  unfold tailWord_200143
  simp only [CollatzResearch.WordTrace]
  refine ⟨7299814913923567548165083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4866543275949045032110055 7299814913923567548165083)
  ·
    refine ⟨10949722370885351322247625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7299814913923567548165083 10949722370885351322247625)
    ·
      refine ⟨8212291778164013491685719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10949722370885351322247625 8212291778164013491685719)
      ·
        refine ⟨12318437667246020237528579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8212291778164013491685719 12318437667246020237528579)
        ·
          refine ⟨18477656500869030356292869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12318437667246020237528579 18477656500869030356292869)
          ·
            refine ⟨3464560593912943191804913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18477656500869030356292869 3464560593912943191804913)
            ·
              refine ⟨2598420445434707393853685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3464560593912943191804913 2598420445434707393853685)
              ·
                refine ⟨243601916759503818173783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2598420445434707393853685 243601916759503818173783)
                ·
                  refine ⟨365402875139255727260675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243601916759503818173783 365402875139255727260675)
                  ·
                    refine ⟨548104312708883590891013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365402875139255727260675 548104312708883590891013)
                    ·
                      refine ⟨102769558632915673292065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 548104312708883590891013 102769558632915673292065)
                      ·
                        rfl

theorem cell23_200143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 4].length) (baseStart_200143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200143 prefixEnd_200143 := by exact prefixLift 200143
  have htrace : WordTrace (prefixWord ++ tailWord_200143) baseStart_200143 baseEnd_200143 := by
    simpa [prefixWord, tailWord_200143, baseEnd_200143] using wordTrace_append hprefix tailTrace_200143
  have hstable : (prefixWord ++ tailWord_200143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200143).length < 2 ^ (prefixWord ++ tailWord_200143).sum := by decide
  have hdescent : baseEnd_200143 < baseStart_200143 := by decide
  rcases family_descends (prefixWord ++ tailWord_200143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200154 : List Nat := [3, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3]
def baseStart_200154 : Nat := 118140960795 + 200154 * 2 ^ 59
def prefixEnd_200154 : Nat := 4983230072969 + 3 ^ 40 * 200154 * 2
def baseEnd_200154 : Nat := 102775206920115130254515

theorem tailTrace_200154 : CollatzResearch.WordTrace tailWord_200154 prefixEnd_200154 102775206920115130254515 := by
  unfold tailWord_200154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825054029220929106703879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4866810744589144284543677 1825054029220929106703879)
  ·
    refine ⟨2737581043831393660055819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1825054029220929106703879 2737581043831393660055819)
    ·
      refine ⟨4106371565747090490083729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2737581043831393660055819 4106371565747090490083729)
      ·
        refine ⟨3079778674310317867562797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4106371565747090490083729 3079778674310317867562797)
        ·
          refine ⟨1154917002866369200336049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3079778674310317867562797 1154917002866369200336049)
          ·
            refine ⟨866187752149776900252037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154917002866369200336049 866187752149776900252037)
            ·
              refine ⟨162410203528083168797257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 866187752149776900252037 162410203528083168797257)
              ·
                refine ⟨121807652646062376597943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162410203528083168797257 121807652646062376597943)
                ·
                  refine ⟨182711478969093564896915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121807652646062376597943 182711478969093564896915)
                  ·
                    refine ⟨274067218453640347345373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182711478969093564896915 274067218453640347345373)
                    ·
                      refine ⟨102775206920115130254515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 274067218453640347345373 102775206920115130254515)
                      ·
                        rfl

theorem cell23_200154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_200154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200154 prefixEnd_200154 := by exact prefixLift 200154
  have htrace : WordTrace (prefixWord ++ tailWord_200154) baseStart_200154 baseEnd_200154 := by
    simpa [prefixWord, tailWord_200154, baseEnd_200154] using wordTrace_append hprefix tailTrace_200154
  have hstable : (prefixWord ++ tailWord_200154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200154).length < 2 ^ (prefixWord ++ tailWord_200154).sum := by decide
  have hdescent : baseEnd_200154 < baseStart_200154 := by decide
  rcases family_descends (prefixWord ++ tailWord_200154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200170 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_200170 : Nat := 118140960795 + 200170 * 2 ^ 59
def prefixEnd_200170 : Nat := 4983230072969 + 3 ^ 40 * 200170 * 2
def baseEnd_200170 : Nat := 34261140870195689218147

theorem tailTrace_200170 : CollatzResearch.WordTrace tailWord_200170 prefixEnd_200170 34261140870195689218147 := by
  unfold tailWord_200170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825199921206437789849491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4867199789883834106265309 1825199921206437789849491)
  ·
    refine ⟨2737799881809656684774237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1825199921206437789849491 2737799881809656684774237)
    ·
      refine ⟨1026674955678621256790339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2737799881809656684774237 1026674955678621256790339)
      ·
        refine ⟨1540012433517931885185509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026674955678621256790339 1540012433517931885185509)
        ·
          refine ⟨288752331284612228472283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1540012433517931885185509 288752331284612228472283)
          ·
            refine ⟨433128496926918342708425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288752331284612228472283 433128496926918342708425)
            ·
              refine ⟨324846372695188757031319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433128496926918342708425 324846372695188757031319)
              ·
                refine ⟨487269559042783135546979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324846372695188757031319 487269559042783135546979)
                ·
                  refine ⟨730904338564174703320469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487269559042783135546979 730904338564174703320469)
                  ·
                    refine ⟨34261140870195689218147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 730904338564174703320469 34261140870195689218147)
                    ·
                      rfl

theorem cell23_200170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_200170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200170 prefixEnd_200170 := by exact prefixLift 200170
  have htrace : WordTrace (prefixWord ++ tailWord_200170) baseStart_200170 baseEnd_200170 := by
    simpa [prefixWord, tailWord_200170, baseEnd_200170] using wordTrace_append hprefix tailTrace_200170
  have hstable : (prefixWord ++ tailWord_200170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200170).length < 2 ^ (prefixWord ++ tailWord_200170).sum := by decide
  have hdescent : baseEnd_200170 < baseStart_200170 := by decide
  rcases family_descends (prefixWord ++ tailWord_200170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200177 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 3, 2, 2]
def baseStart_200177 : Nat := 118140960795 + 200177 * 2 ^ 59
def prefixEnd_200177 : Nat := 4983230072969 + 3 ^ 40 * 200177 * 2
def baseEnd_200177 : Nat := 102787016975168540266909

theorem tailTrace_200177 : CollatzResearch.WordTrace tailWord_200177 prefixEnd_200177 102787016975168540266909 := by
  unfold tailWord_200177
  simp only [CollatzResearch.WordTrace]
  refine ⟨7301054995800391354902785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4867369997200260903268523 7301054995800391354902785)
  ·
    refine ⟨5475791246850293516177089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7301054995800391354902785 5475791246850293516177089)
    ·
      refine ⟨4106843435137720137132817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5475791246850293516177089 4106843435137720137132817)
      ·
        refine ⟨3080132576353290102849613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4106843435137720137132817 3080132576353290102849613)
        ·
          refine ⟨1155049716132483788568605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3080132576353290102849613 1155049716132483788568605)
          ·
            refine ⟨433143643549681420713227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1155049716132483788568605 433143643549681420713227)
            ·
              refine ⟨649715465324522131069841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433143643549681420713227 649715465324522131069841)
              ·
                refine ⟨487286598993391598302381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649715465324522131069841 487286598993391598302381)
                ·
                  refine ⟨182732474622521849363393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487286598993391598302381 182732474622521849363393)
                  ·
                    refine ⟨137049355966891387022545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 182732474622521849363393 137049355966891387022545)
                    ·
                      refine ⟨102787016975168540266909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137049355966891387022545 102787016975168540266909)
                      ·
                        rfl

theorem cell23_200177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_200177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200177 prefixEnd_200177 := by exact prefixLift 200177
  have htrace : WordTrace (prefixWord ++ tailWord_200177) baseStart_200177 baseEnd_200177 := by
    simpa [prefixWord, tailWord_200177, baseEnd_200177] using wordTrace_append hprefix tailTrace_200177
  have hstable : (prefixWord ++ tailWord_200177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200177).length < 2 ^ (prefixWord ++ tailWord_200177).sum := by decide
  have hdescent : baseEnd_200177 < baseStart_200177 := by decide
  rcases family_descends (prefixWord ++ tailWord_200177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200194 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_200194 : Nat := 118140960795 + 200194 * 2 ^ 59
def prefixEnd_200194 : Nat := 4983230072969 + 3 ^ 40 * 200194 * 2
def baseEnd_200194 : Nat := 102795746146294973754331

theorem tailTrace_200194 : CollatzResearch.WordTrace tailWord_200194 prefixEnd_200194 102795746146294973754331 := by
  unfold tailWord_200194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825418759184700814567909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4867783357825868838847757 1825418759184700814567909)
  ·
    refine ⟨342266017347131402731483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1825418759184700814567909 342266017347131402731483)
    ·
      refine ⟨513399026020697104097225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342266017347131402731483 513399026020697104097225)
      ·
        refine ⟨385049269515522828072919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513399026020697104097225 385049269515522828072919)
        ·
          refine ⟨577573904273284242109379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385049269515522828072919 577573904273284242109379)
          ·
            refine ⟨866360856409926363164069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577573904273284242109379 866360856409926363164069)
            ·
              refine ⟨162442660576861193093263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 866360856409926363164069 162442660576861193093263)
              ·
                refine ⟨243663990865291789639895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162442660576861193093263 243663990865291789639895)
                ·
                  refine ⟨365495986297937684459843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243663990865291789639895 365495986297937684459843)
                  ·
                    refine ⟨548243979446906526689765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365495986297937684459843 548243979446906526689765)
                    ·
                      refine ⟨102795746146294973754331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 548243979446906526689765 102795746146294973754331)
                      ·
                        rfl

theorem cell23_200194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_200194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200194 prefixEnd_200194 := by exact prefixLift 200194
  have htrace : WordTrace (prefixWord ++ tailWord_200194) baseStart_200194 baseEnd_200194 := by
    simpa [prefixWord, tailWord_200194, baseEnd_200194] using wordTrace_append hprefix tailTrace_200194
  have hstable : (prefixWord ++ tailWord_200194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200194).length < 2 ^ (prefixWord ++ tailWord_200194).sum := by decide
  have hdescent : baseEnd_200194 < baseStart_200194 := by decide
  rcases family_descends (prefixWord ++ tailWord_200194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200204 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_200204 : Nat := 118140960795 + 200204 * 2 ^ 59
def prefixEnd_200204 : Nat := 4983230072969 + 3 ^ 40 * 200204 * 2
def baseEnd_200204 : Nat := 34266960317613311543095

theorem tailTrace_200204 : CollatzResearch.WordTrace tailWord_200204 prefixEnd_200204 34266960317613311543095 := by
  unfold tailWord_200204
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651019883351287483067833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4868026511135049977423777 3651019883351287483067833)
  ·
    refine ⟨2738264912513465612300875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3651019883351287483067833 2738264912513465612300875)
    ·
      refine ⟨4107397368770198418451313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2738264912513465612300875 4107397368770198418451313)
      ·
        refine ⟨3080548026577648813838485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4107397368770198418451313 3080548026577648813838485)
        ·
          refine ⟨144400688745827288148679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3080548026577648813838485 144400688745827288148679)
          ·
            refine ⟨216601033118740932223019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144400688745827288148679 216601033118740932223019)
            ·
              refine ⟨324901549678111398334529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216601033118740932223019 324901549678111398334529)
              ·
                refine ⟨243676162258583548750897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324901549678111398334529 243676162258583548750897)
                ·
                  refine ⟨182757121693937661563173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243676162258583548750897 182757121693937661563173)
                  ·
                    refine ⟨34266960317613311543095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 182757121693937661563173 34266960317613311543095)
                    ·
                      rfl

theorem cell23_200204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_200204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200204 prefixEnd_200204 := by exact prefixLift 200204
  have htrace : WordTrace (prefixWord ++ tailWord_200204) baseStart_200204 baseEnd_200204 := by
    simpa [prefixWord, tailWord_200204, baseEnd_200204] using wordTrace_append hprefix tailTrace_200204
  have hstable : (prefixWord ++ tailWord_200204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200204).length < 2 ^ (prefixWord ++ tailWord_200204).sum := by decide
  have hdescent : baseEnd_200204 < baseStart_200204 := by decide
  rcases family_descends (prefixWord ++ tailWord_200204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200227 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 3]
def baseStart_200227 : Nat := 118140960795 + 200227 * 2 ^ 59
def prefixEnd_200227 : Nat := 4983230072969 + 3 ^ 40 * 200227 * 2
def baseEnd_200227 : Nat := 102812691007893344641679

theorem tailTrace_200227 : CollatzResearch.WordTrace tailWord_200227 prefixEnd_200227 102812691007893344641679 := by
  unfold tailWord_200227
  simp only [CollatzResearch.WordTrace]
  refine ⟨7302878645619249894222935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4868585763746166596148623 7302878645619249894222935)
  ·
    refine ⟨10954317968428874841334403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7302878645619249894222935 10954317968428874841334403)
    ·
      refine ⟨16431476952643312262001605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10954317968428874841334403 16431476952643312262001605)
      ·
        refine ⟨3080901928620621049125301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16431476952643312262001605 3080901928620621049125301)
        ·
          refine ⟨288834555808183223355497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3080901928620621049125301 288834555808183223355497)
          ·
            refine ⟨216625916856137417516623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288834555808183223355497 216625916856137417516623)
            ·
              refine ⟨324938875284206126274935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216625916856137417516623 324938875284206126274935)
              ·
                refine ⟨487408312926309189412403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324938875284206126274935 487408312926309189412403)
                ·
                  refine ⟨731112469389463784118605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487408312926309189412403 731112469389463784118605)
                  ·
                    refine ⟨274167176021048919044477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 731112469389463784118605 274167176021048919044477)
                    ·
                      refine ⟨102812691007893344641679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 274167176021048919044477 102812691007893344641679)
                      ·
                        rfl

theorem cell23_200227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_200227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200227 prefixEnd_200227 := by exact prefixLift 200227
  have htrace : WordTrace (prefixWord ++ tailWord_200227) baseStart_200227 baseEnd_200227 := by
    simpa [prefixWord, tailWord_200227, baseEnd_200227] using wordTrace_append hprefix tailTrace_200227
  have hstable : (prefixWord ++ tailWord_200227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200227).length < 2 ^ (prefixWord ++ tailWord_200227).sum := by decide
  have hdescent : baseEnd_200227 < baseStart_200227 := by decide
  rcases family_descends (prefixWord ++ tailWord_200227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200250 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2]
def baseStart_200250 : Nat := 118140960795 + 200250 * 2 ^ 59
def prefixEnd_200250 : Nat := 4983230072969 + 3 ^ 40 * 200250 * 2
def baseEnd_200250 : Nat := 102824501062946754654073

theorem tailTrace_200250 : CollatzResearch.WordTrace tailWord_200250 prefixEnd_200250 102824501062946754654073 := by
  unfold tailWord_200250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825929381133981205577551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4869145016357283214873469 1825929381133981205577551)
  ·
    refine ⟨2738894071700971808366327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1825929381133981205577551 2738894071700971808366327)
    ·
      refine ⟨4108341107551457712549491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2738894071700971808366327 4108341107551457712549491)
      ·
        refine ⟨6162511661327186568824237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4108341107551457712549491 6162511661327186568824237)
        ·
          refine ⟨2310941872997694963309089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6162511661327186568824237 2310941872997694963309089)
          ·
            refine ⟨1733206404748271222481817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2310941872997694963309089 1733206404748271222481817)
            ·
              refine ⟨1299904803561203416861363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733206404748271222481817 1299904803561203416861363)
              ·
                refine ⟨1949857205341805125292045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299904803561203416861363 1949857205341805125292045)
                ·
                  refine ⟨731196452003176921984517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1949857205341805125292045 731196452003176921984517)
                  ·
                    refine ⟨137099334750595672872097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 731196452003176921984517 137099334750595672872097)
                    ·
                      refine ⟨102824501062946754654073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137099334750595672872097 102824501062946754654073)
                      ·
                        rfl

theorem cell23_200250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_200250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200250 prefixEnd_200250 := by exact prefixLift 200250
  have htrace : WordTrace (prefixWord ++ tailWord_200250) baseStart_200250 baseEnd_200250 := by
    simpa [prefixWord, tailWord_200250, baseEnd_200250] using wordTrace_append hprefix tailTrace_200250
  have hstable : (prefixWord ++ tailWord_200250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200250).length < 2 ^ (prefixWord ++ tailWord_200250).sum := by decide
  have hdescent : baseEnd_200250 < baseStart_200250 := by decide
  rcases family_descends (prefixWord ++ tailWord_200250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200267 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 2, 2, 2]
def baseStart_200267 : Nat := 118140960795 + 200267 * 2 ^ 59
def prefixEnd_200267 : Nat := 4983230072969 + 3 ^ 40 * 200267 * 2
def baseEnd_200267 : Nat := 102833230234073188141495

theorem tailTrace_200267 : CollatzResearch.WordTrace tailWord_200267 prefixEnd_200267 102833230234073188141495 := by
  unfold tailWord_200267
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304337565474336725679055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4869558376982891150452703 7304337565474336725679055)
  ·
    refine ⟨10956506348211505088518583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7304337565474336725679055 10956506348211505088518583)
    ·
      refine ⟨16434759522317257632777875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10956506348211505088518583 16434759522317257632777875)
      ·
        refine ⟨24652139283475886449166813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16434759522317257632777875 24652139283475886449166813)
        ·
          refine ⟨9244552231303457418437555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24652139283475886449166813 9244552231303457418437555)
          ·
            refine ⟨13866828346955186127656333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244552231303457418437555 13866828346955186127656333)
            ·
              refine ⟨5200060630108194797871125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13866828346955186127656333 5200060630108194797871125)
              ·
                refine ⟨243752842036321631150209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5200060630108194797871125 243752842036321631150209)
                ·
                  refine ⟨182814631527241223362657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243752842036321631150209 182814631527241223362657)
                  ·
                    refine ⟨137110973645430917521993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 182814631527241223362657 137110973645430917521993)
                    ·
                      refine ⟨102833230234073188141495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137110973645430917521993 102833230234073188141495)
                      ·
                        rfl

theorem cell23_200267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 2, 2].length) (baseStart_200267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200267 prefixEnd_200267 := by exact prefixLift 200267
  have htrace : WordTrace (prefixWord ++ tailWord_200267) baseStart_200267 baseEnd_200267 := by
    simpa [prefixWord, tailWord_200267, baseEnd_200267] using wordTrace_append hprefix tailTrace_200267
  have hstable : (prefixWord ++ tailWord_200267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200267).length < 2 ^ (prefixWord ++ tailWord_200267).sum := by decide
  have hdescent : baseEnd_200267 < baseStart_200267 := by decide
  rcases family_descends (prefixWord ++ tailWord_200267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200278 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_200278 : Nat := 118140960795 + 200278 * 2 ^ 59
def prefixEnd_200278 : Nat := 4983230072969 + 3 ^ 40 * 200278 * 2
def baseEnd_200278 : Nat := 102838878521272645103945

theorem tailTrace_200278 : CollatzResearch.WordTrace tailWord_200278 prefixEnd_200278 102838878521272645103945 := by
  unfold tailWord_200278
  simp only [CollatzResearch.WordTrace]
  refine ⟨456546173027155350270593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4869825845622990402886325 456546173027155350270593)
  ·
    refine ⟨342409629770366512702945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 456546173027155350270593 342409629770366512702945)
    ·
      refine ⟨256807222327774884527209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342409629770366512702945 256807222327774884527209)
      ·
        refine ⟨192605416745831163395407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256807222327774884527209 192605416745831163395407)
        ·
          refine ⟨288908125118746745093111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192605416745831163395407 288908125118746745093111)
          ·
            refine ⟨433362187678120117639667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288908125118746745093111 433362187678120117639667)
            ·
              refine ⟨650043281517180176459501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433362187678120117639667 650043281517180176459501)
              ·
                refine ⟨243766230568942566172313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650043281517180176459501 243766230568942566172313)
                ·
                  refine ⟨182824672926706924629235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243766230568942566172313 182824672926706924629235)
                  ·
                    refine ⟨274237009390060386943853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182824672926706924629235 274237009390060386943853)
                    ·
                      refine ⟨102838878521272645103945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 274237009390060386943853 102838878521272645103945)
                      ·
                        rfl

theorem cell23_200278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_200278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200278 prefixEnd_200278 := by exact prefixLift 200278
  have htrace : WordTrace (prefixWord ++ tailWord_200278) baseStart_200278 baseEnd_200278 := by
    simpa [prefixWord, tailWord_200278, baseEnd_200278] using wordTrace_append hprefix tailTrace_200278
  have hstable : (prefixWord ++ tailWord_200278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200278).length < 2 ^ (prefixWord ++ tailWord_200278).sum := by decide
  have hdescent : baseEnd_200278 < baseStart_200278 := by decide
  rcases family_descends (prefixWord ++ tailWord_200278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200313 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_200313 : Nat := 118140960795 + 200313 * 2 ^ 59
def prefixEnd_200313 : Nat := 4983230072969 + 3 ^ 40 * 200313 * 2
def baseEnd_200313 : Nat := 102856850344180008166283

theorem tailTrace_200313 : CollatzResearch.WordTrace tailWord_200313 prefixEnd_200313 102856850344180008166283 := by
  unfold tailWord_200313
  simp only [CollatzResearch.WordTrace]
  refine ⟨7306015323307686581853593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4870676882205124387902395 7306015323307686581853593)
  ·
    refine ⟨5479511492480764936390195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7306015323307686581853593 5479511492480764936390195)
    ·
      refine ⟨8219267238721147404585293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5479511492480764936390195 8219267238721147404585293)
      ·
        refine ⟨3082225214520430276719485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8219267238721147404585293 3082225214520430276719485)
        ·
          refine ⟨1155834455445161353769807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3082225214520430276719485 1155834455445161353769807)
          ·
            refine ⟨1733751683167742030654711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155834455445161353769807 1733751683167742030654711)
            ·
              refine ⟨2600627524751613045982067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733751683167742030654711 2600627524751613045982067)
              ·
                refine ⟨3900941287127419568973101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600627524751613045982067 3900941287127419568973101)
                ·
                  refine ⟨1462852982672782338364913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3900941287127419568973101 1462852982672782338364913)
                  ·
                    refine ⟨1097139737004586753773685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1462852982672782338364913 1097139737004586753773685)
                    ·
                      refine ⟨102856850344180008166283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1097139737004586753773685 102856850344180008166283)
                      ·
                        rfl

theorem cell23_200313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_200313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200313 prefixEnd_200313 := by exact prefixLift 200313
  have htrace : WordTrace (prefixWord ++ tailWord_200313) baseStart_200313 baseEnd_200313 := by
    simpa [prefixWord, tailWord_200313, baseEnd_200313] using wordTrace_append hprefix tailTrace_200313
  have hstable : (prefixWord ++ tailWord_200313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200313).length < 2 ^ (prefixWord ++ tailWord_200313).sum := by decide
  have hdescent : baseEnd_200313 < baseStart_200313 := by decide
  rcases family_descends (prefixWord ++ tailWord_200313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200323 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 4]
def baseStart_200323 : Nat := 118140960795 + 200323 * 2 ^ 59
def prefixEnd_200323 : Nat := 4983230072969 + 3 ^ 40 * 200323 * 2
def baseEnd_200323 : Nat := 102861985150724969041237

theorem tailTrace_200323 : CollatzResearch.WordTrace tailWord_200323 prefixEnd_200323 102861985150724969041237 := by
  unfold tailWord_200323
  simp only [CollatzResearch.WordTrace]
  refine ⟨7306380053271458289717623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4870920035514305526478415 7306380053271458289717623)
  ·
    refine ⟨10959570079907187434576435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7306380053271458289717623 10959570079907187434576435)
    ·
      refine ⟨16439355119860781151864653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10959570079907187434576435 16439355119860781151864653)
      ·
        refine ⟨6164758169947792931949245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16439355119860781151864653 6164758169947792931949245)
        ·
          refine ⟨2311784313730422349480967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6164758169947792931949245 2311784313730422349480967)
          ·
            refine ⟨3467676470595633524221451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311784313730422349480967 3467676470595633524221451)
            ·
              refine ⟨5201514705893450286332177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3467676470595633524221451 5201514705893450286332177)
              ·
                refine ⟨3901136029420087714749133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5201514705893450286332177 3901136029420087714749133)
                ·
                  refine ⟨1462926011032532893030925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3901136029420087714749133 1462926011032532893030925)
                  ·
                    refine ⟨548597254137199834886597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1462926011032532893030925 548597254137199834886597)
                    ·
                      refine ⟨102861985150724969041237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 548597254137199834886597 102861985150724969041237)
                      ·
                        rfl

theorem cell23_200323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_200323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200323 prefixEnd_200323 := by exact prefixLift 200323
  have htrace : WordTrace (prefixWord ++ tailWord_200323) baseStart_200323 baseEnd_200323 := by
    simpa [prefixWord, tailWord_200323, baseEnd_200323] using wordTrace_append hprefix tailTrace_200323
  have hstable : (prefixWord ++ tailWord_200323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200323).length < 2 ^ (prefixWord ++ tailWord_200323).sum := by decide
  have hdescent : baseEnd_200323 < baseStart_200323 := by decide
  rcases family_descends (prefixWord ++ tailWord_200323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200330 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_200330 : Nat := 118140960795 + 200330 * 2 ^ 59
def prefixEnd_200330 : Nat := 4983230072969 + 3 ^ 40 * 200330 * 2
def baseEnd_200330 : Nat := 102865579515306441653705

theorem tailTrace_200330 : CollatzResearch.WordTrace tailWord_200330 prefixEnd_200330 102865579515306441653705 := by
  unfold tailWord_200330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826658841061524621305611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4871090242830732323481629 1826658841061524621305611)
  ·
    refine ⟨2739988261592286931958417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1826658841061524621305611 2739988261592286931958417)
    ·
      refine ⟨2054991196194215198968813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2739988261592286931958417 2054991196194215198968813)
      ·
        refine ⟨770621698572830699613305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2054991196194215198968813 770621698572830699613305)
        ·
          refine ⟨577966273929623024709979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770621698572830699613305 577966273929623024709979)
          ·
            refine ⟨866949410894434537064969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577966273929623024709979 866949410894434537064969)
            ·
              refine ⟨650212058170825902798727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866949410894434537064969 650212058170825902798727)
              ·
                refine ⟨975318087256238854198091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650212058170825902798727 975318087256238854198091)
                ·
                  refine ⟨1462977130884358281297137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975318087256238854198091 1462977130884358281297137)
                  ·
                    refine ⟨1097232848163268710972853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1462977130884358281297137 1097232848163268710972853)
                    ·
                      refine ⟨102865579515306441653705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1097232848163268710972853 102865579515306441653705)
                      ·
                        rfl

theorem cell23_200330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_200330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200330 prefixEnd_200330 := by exact prefixLift 200330
  have htrace : WordTrace (prefixWord ++ tailWord_200330) baseStart_200330 baseEnd_200330 := by
    simpa [prefixWord, tailWord_200330, baseEnd_200330] using wordTrace_append hprefix tailTrace_200330
  have hstable : (prefixWord ++ tailWord_200330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200330).length < 2 ^ (prefixWord ++ tailWord_200330).sum := by decide
  have hdescent : baseEnd_200330 < baseStart_200330 := by decide
  rcases family_descends (prefixWord ++ tailWord_200330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200380 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 8]
def baseStart_200380 : Nat := 118140960795 + 200380 * 2 ^ 59
def prefixEnd_200380 : Nat := 4983230072969 + 3 ^ 40 * 200380 * 2
def baseEnd_200380 : Nat := 11432361505336805114275

theorem tailTrace_200380 : CollatzResearch.WordTrace tailWord_200380 prefixEnd_200380 11432361505336805114275 := by
  unfold tailWord_200380
  simp only [CollatzResearch.WordTrace]
  refine ⟨3654229507032478512271297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4872306009376638016361729 3654229507032478512271297)
  ·
    refine ⟨2740672130274358884203473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3654229507032478512271297 2740672130274358884203473)
    ·
      refine ⟨2055504097705769163152605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2740672130274358884203473 2055504097705769163152605)
      ·
        refine ⟨770814036639663436182227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2055504097705769163152605 770814036639663436182227)
        ·
          refine ⟨1156221054959495154273341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770814036639663436182227 1156221054959495154273341)
          ·
            refine ⟨433582895609810682852503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1156221054959495154273341 433582895609810682852503)
            ·
              refine ⟨650374343414716024278755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433582895609810682852503 650374343414716024278755)
              ·
                refine ⟨975561515122074036418133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650374343414716024278755 975561515122074036418133)
                ·
                  refine ⟨11432361505336805114275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 975561515122074036418133 11432361505336805114275)
                  ·
                    rfl

theorem cell23_200380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_200380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200380 prefixEnd_200380 := by exact prefixLift 200380
  have htrace : WordTrace (prefixWord ++ tailWord_200380) baseStart_200380 baseEnd_200380 := by
    simpa [prefixWord, tailWord_200380, baseEnd_200380] using wordTrace_append hprefix tailTrace_200380
  have hstable : (prefixWord ++ tailWord_200380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200380).length < 2 ^ (prefixWord ++ tailWord_200380).sum := by decide
  have hdescent : baseEnd_200380 < baseStart_200380 := by decide
  rcases family_descends (prefixWord ++ tailWord_200380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200383 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_200383 : Nat := 118140960795 + 200383 * 2 ^ 59
def prefixEnd_200383 : Nat := 4983230072969 + 3 ^ 40 * 200383 * 2
def baseEnd_200383 : Nat := 102892793989994734290961

theorem tailTrace_200383 : CollatzResearch.WordTrace tailWord_200383 prefixEnd_200383 102892793989994734290961 := by
  unfold tailWord_200383
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308568433054088536901803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4872378955369392357934535 7308568433054088536901803)
  ·
    refine ⟨10962852649581132805352705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7308568433054088536901803 10962852649581132805352705)
    ·
      refine ⟨8222139487185849604014529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10962852649581132805352705 8222139487185849604014529)
      ·
        refine ⟨6166604615389387203010897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8222139487185849604014529 6166604615389387203010897)
        ·
          refine ⟨4624953461542040402258173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6166604615389387203010897 4624953461542040402258173)
          ·
            refine ⟨1734357548078265150846815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4624953461542040402258173 1734357548078265150846815)
            ·
              refine ⟨2601536322117397726270223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734357548078265150846815 2601536322117397726270223)
              ·
                refine ⟨3902304483176096589405335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601536322117397726270223 3902304483176096589405335)
                ·
                  refine ⟨5853456724764144884108003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902304483176096589405335 5853456724764144884108003)
                  ·
                    refine ⟨8780185087146217326162005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5853456724764144884108003 8780185087146217326162005)
                    ·
                      refine ⟨102892793989994734290961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 8780185087146217326162005 102892793989994734290961)
                      ·
                        rfl

theorem cell23_200383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_200383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200383 prefixEnd_200383 := by exact prefixLift 200383
  have htrace : WordTrace (prefixWord ++ tailWord_200383) baseStart_200383 baseEnd_200383 := by
    simpa [prefixWord, tailWord_200383, baseEnd_200383] using wordTrace_append hprefix tailTrace_200383
  have hstable : (prefixWord ++ tailWord_200383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200383).length < 2 ^ (prefixWord ++ tailWord_200383).sum := by decide
  have hdescent : baseEnd_200383 < baseStart_200383 := by decide
  rcases family_descends (prefixWord ++ tailWord_200383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200403 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 5]
def baseStart_200403 : Nat := 118140960795 + 200403 * 2 ^ 59
def prefixEnd_200403 : Nat := 4983230072969 + 3 ^ 40 * 200403 * 2
def baseEnd_200403 : Nat := 102903063603084656040869

theorem tailTrace_200403 : CollatzResearch.WordTrace tailWord_200403 prefixEnd_200403 102903063603084656040869 := by
  unfold tailWord_200403
  simp only [CollatzResearch.WordTrace]
  refine ⟨7309297892981631952629863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4872865261987754635086575 7309297892981631952629863)
  ·
    refine ⟨10963946839472447928944795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7309297892981631952629863 10963946839472447928944795)
    ·
      refine ⟨16445920259208671893417193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10963946839472447928944795 16445920259208671893417193)
      ·
        refine ⟨12334440194406503920062895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16445920259208671893417193 12334440194406503920062895)
        ·
          refine ⟨18501660291609755880094343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12334440194406503920062895 18501660291609755880094343)
          ·
            refine ⟨27752490437414633820141515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18501660291609755880094343 27752490437414633820141515)
            ·
              refine ⟨41628735656121950730212273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27752490437414633820141515 41628735656121950730212273)
              ·
                refine ⟨31221551742091463047659205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41628735656121950730212273 31221551742091463047659205)
                ·
                  refine ⟨5854040951642149321436101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31221551742091463047659205 5854040951642149321436101)
                  ·
                    refine ⟨1097632678432902997769269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854040951642149321436101 1097632678432902997769269)
                    ·
                      refine ⟨102903063603084656040869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1097632678432902997769269 102903063603084656040869)
                      ·
                        rfl

theorem cell23_200403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_200403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200403 prefixEnd_200403 := by exact prefixLift 200403
  have htrace : WordTrace (prefixWord ++ tailWord_200403) baseStart_200403 baseEnd_200403 := by
    simpa [prefixWord, tailWord_200403, baseEnd_200403] using wordTrace_append hprefix tailTrace_200403
  have hstable : (prefixWord ++ tailWord_200403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200403).length < 2 ^ (prefixWord ++ tailWord_200403).sum := by decide
  have hdescent : baseEnd_200403 < baseStart_200403 := by decide
  rcases family_descends (prefixWord ++ tailWord_200403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200407 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 3]
def baseStart_200407 : Nat := 118140960795 + 200407 * 2 ^ 59
def prefixEnd_200407 : Nat := 4983230072969 + 3 ^ 40 * 200407 * 2
def baseEnd_200407 : Nat := 102905117525702640390851

theorem tailTrace_200407 : CollatzResearch.WordTrace tailWord_200407 prefixEnd_200407 102905117525702640390851 := by
  unfold tailWord_200407
  simp only [CollatzResearch.WordTrace]
  refine ⟨7309443784967140635775475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4872962523311427090516983 7309443784967140635775475)
  ·
    refine ⟨10964165677450710953663213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7309443784967140635775475 10964165677450710953663213)
    ·
      refine ⟨4111562129044016607623705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10964165677450710953663213 4111562129044016607623705)
      ·
        refine ⟨3083671596783012455717779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4111562129044016607623705 3083671596783012455717779)
        ·
          refine ⟨4625507395174518683576669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083671596783012455717779 4625507395174518683576669)
          ·
            refine ⟨1734565273190444506341251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4625507395174518683576669 1734565273190444506341251)
            ·
              refine ⟨2601847909785666759511877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734565273190444506341251 2601847909785666759511877)
              ·
                refine ⟨487846483084812517408477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2601847909785666759511877 487846483084812517408477)
                ·
                  refine ⟨182942431156804694028179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487846483084812517408477 182942431156804694028179)
                  ·
                    refine ⟨274413646735207041042269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182942431156804694028179 274413646735207041042269)
                    ·
                      refine ⟨102905117525702640390851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 274413646735207041042269 102905117525702640390851)
                      ·
                        rfl

theorem cell23_200407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_200407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200407 prefixEnd_200407 := by exact prefixLift 200407
  have htrace : WordTrace (prefixWord ++ tailWord_200407) baseStart_200407 baseEnd_200407 := by
    simpa [prefixWord, tailWord_200407, baseEnd_200407] using wordTrace_append hprefix tailTrace_200407
  have hstable : (prefixWord ++ tailWord_200407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200407).length < 2 ^ (prefixWord ++ tailWord_200407).sum := by decide
  have hdescent : baseEnd_200407 < baseStart_200407 := by decide
  rcases family_descends (prefixWord ++ tailWord_200407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200434 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_200434 : Nat := 118140960795 + 200434 * 2 ^ 59
def prefixEnd_200434 : Nat := 4983230072969 + 3 ^ 40 * 200434 * 2
def baseEnd_200434 : Nat := 102918981503374034753227

theorem tailTrace_200434 : CollatzResearch.WordTrace tailWord_200434 prefixEnd_200434 102918981503374034753227 := by
  unfold tailWord_200434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1827607138967331061752089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4873619037246216164672237 1827607138967331061752089)
  ·
    refine ⟨1370705354225498296314067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1827607138967331061752089 1370705354225498296314067)
    ·
      refine ⟨2056058031338247444471101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370705354225498296314067 2056058031338247444471101)
      ·
        refine ⟨771021761751842791676663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2056058031338247444471101 771021761751842791676663)
        ·
          refine ⟨1156532642627764187514995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771021761751842791676663 1156532642627764187514995)
          ·
            refine ⟨1734798963941646281272493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156532642627764187514995 1734798963941646281272493)
            ·
              refine ⟨650549611478117355477185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1734798963941646281272493 650549611478117355477185)
              ·
                refine ⟨487912208608588016607889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650549611478117355477185 487912208608588016607889)
                ·
                  refine ⟨365934156456441012455917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487912208608588016607889 365934156456441012455917)
                  ·
                    refine ⟨137225308671165379670969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365934156456441012455917 137225308671165379670969)
                    ·
                      refine ⟨102918981503374034753227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137225308671165379670969 102918981503374034753227)
                      ·
                        rfl

theorem cell23_200434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_200434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200434 prefixEnd_200434 := by exact prefixLift 200434
  have htrace : WordTrace (prefixWord ++ tailWord_200434) baseStart_200434 baseEnd_200434 := by
    simpa [prefixWord, tailWord_200434, baseEnd_200434] using wordTrace_append hprefix tailTrace_200434
  have hstable : (prefixWord ++ tailWord_200434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200434).length < 2 ^ (prefixWord ++ tailWord_200434).sum := by decide
  have hdescent : baseEnd_200434 < baseStart_200434 := by decide
  rcases family_descends (prefixWord ++ tailWord_200434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200460 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_200460 : Nat := 118140960795 + 200460 * 2 ^ 59
def prefixEnd_200460 : Nat := 4983230072969 + 3 ^ 40 * 200460 * 2
def baseEnd_200460 : Nat := 102932332000390933028107

theorem tailTrace_200460 : CollatzResearch.WordTrace tailWord_200460 prefixEnd_200460 102932332000390933028107 := by
  unfold tailWord_200460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3655688426887565343727417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4874251235850087124969889 3655688426887565343727417)
  ·
    refine ⟨2741766320165674007795563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3655688426887565343727417 2741766320165674007795563)
    ·
      refine ⟨4112649480248511011693345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2741766320165674007795563 4112649480248511011693345)
      ·
        refine ⟨3084487110186383258770009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4112649480248511011693345 3084487110186383258770009)
        ·
          refine ⟨2313365332639787444077507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3084487110186383258770009 2313365332639787444077507)
          ·
            refine ⟨3470047998959681166116261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313365332639787444077507 3470047998959681166116261)
            ·
              refine ⟨650633999804940218646799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3470047998959681166116261 650633999804940218646799)
              ·
                refine ⟨975950999707410327970199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650633999804940218646799 975950999707410327970199)
                ·
                  refine ⟨1463926499561115491955299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975950999707410327970199 1463926499561115491955299)
                  ·
                    refine ⟨2195889749341673237932949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1463926499561115491955299 2195889749341673237932949)
                    ·
                      refine ⟨102932332000390933028107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2195889749341673237932949 102932332000390933028107)
                      ·
                        rfl

theorem cell23_200460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_200460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200460 prefixEnd_200460 := by exact prefixLift 200460
  have htrace : WordTrace (prefixWord ++ tailWord_200460) baseStart_200460 baseEnd_200460 := by
    simpa [prefixWord, tailWord_200460, baseEnd_200460] using wordTrace_append hprefix tailTrace_200460
  have hstable : (prefixWord ++ tailWord_200460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200460).length < 2 ^ (prefixWord ++ tailWord_200460).sum := by decide
  have hdescent : baseEnd_200460 < baseStart_200460 := by decide
  rcases family_descends (prefixWord ++ tailWord_200460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200467 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 3]
def baseStart_200467 : Nat := 118140960795 + 200467 * 2 ^ 59
def prefixEnd_200467 : Nat := 4983230072969 + 3 ^ 40 * 200467 * 2
def baseEnd_200467 : Nat := 102935926364972405640575

theorem tailTrace_200467 : CollatzResearch.WordTrace tailWord_200467 prefixEnd_200467 102935926364972405640575 := by
  unfold tailWord_200467
  simp only [CollatzResearch.WordTrace]
  refine ⟨7311632164749770882959655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4874421443166513921973103 7311632164749770882959655)
  ·
    refine ⟨10967448247124656324439483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7311632164749770882959655 10967448247124656324439483)
    ·
      refine ⟨16451172370686984486659225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10967448247124656324439483 16451172370686984486659225)
      ·
        refine ⟨12338379278015238364994419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16451172370686984486659225 12338379278015238364994419)
        ·
          refine ⟨18507568917022857547491629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12338379278015238364994419 18507568917022857547491629)
          ·
            refine ⟨6940338343883571580309361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18507568917022857547491629 6940338343883571580309361)
            ·
              refine ⟨5205253757912678685232021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6940338343883571580309361 5205253757912678685232021)
              ·
                refine ⟨243996269902156813370251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5205253757912678685232021 243996269902156813370251)
                ·
                  refine ⟨365994404853235220055377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243996269902156813370251 365994404853235220055377)
                  ·
                    refine ⟨274495803639926415041533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 365994404853235220055377 274495803639926415041533)
                    ·
                      refine ⟨102935926364972405640575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 274495803639926415041533 102935926364972405640575)
                      ·
                        rfl

theorem cell23_200467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 3].length) (baseStart_200467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200467 prefixEnd_200467 := by exact prefixLift 200467
  have htrace : WordTrace (prefixWord ++ tailWord_200467) baseStart_200467 baseEnd_200467 := by
    simpa [prefixWord, tailWord_200467, baseEnd_200467] using wordTrace_append hprefix tailTrace_200467
  have hstable : (prefixWord ++ tailWord_200467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200467).length < 2 ^ (prefixWord ++ tailWord_200467).sum := by decide
  have hdescent : baseEnd_200467 < baseStart_200467 := by decide
  rcases family_descends (prefixWord ++ tailWord_200467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200484 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_200484 : Nat := 118140960795 + 200484 * 2 ^ 59
def prefixEnd_200484 : Nat := 4983230072969 + 3 ^ 40 * 200484 * 2
def baseEnd_200484 : Nat := 102944655536098839127997

theorem tailTrace_200484 : CollatzResearch.WordTrace tailWord_200484 prefixEnd_200484 102944655536098839127997 := by
  unfold tailWord_200484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3656126102844091393164253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4874834803792121857552337 3656126102844091393164253)
  ·
    refine ⟨1371047288566534272436595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3656126102844091393164253 1371047288566534272436595)
    ·
      refine ⟨2056570932849801408654893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371047288566534272436595 2056570932849801408654893)
      ·
        refine ⟨771214099818675528245585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2056570932849801408654893 771214099818675528245585)
        ·
          refine ⟨578410574864006646184189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771214099818675528245585 578410574864006646184189)
          ·
            refine ⟨216903965574002492319071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 578410574864006646184189 216903965574002492319071)
            ·
              refine ⟨325355948361003738478607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216903965574002492319071 325355948361003738478607)
              ·
                refine ⟨488033922541505607717911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325355948361003738478607 488033922541505607717911)
                ·
                  refine ⟨732050883812258411576867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488033922541505607717911 732050883812258411576867)
                  ·
                    refine ⟨1098076325718387617365301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 732050883812258411576867 1098076325718387617365301)
                    ·
                      refine ⟨102944655536098839127997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1098076325718387617365301 102944655536098839127997)
                      ·
                        rfl

theorem cell23_200484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_200484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200484 prefixEnd_200484 := by exact prefixLift 200484
  have htrace : WordTrace (prefixWord ++ tailWord_200484) baseStart_200484 baseEnd_200484 := by
    simpa [prefixWord, tailWord_200484, baseEnd_200484] using wordTrace_append hprefix tailTrace_200484
  have hstable : (prefixWord ++ tailWord_200484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200484).length < 2 ^ (prefixWord ++ tailWord_200484).sum := by decide
  have hdescent : baseEnd_200484 < baseStart_200484 := by decide
  rcases family_descends (prefixWord ++ tailWord_200484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200498 : List Nat := [3, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2]
def baseStart_200498 : Nat := 118140960795 + 200498 * 2 ^ 59
def prefixEnd_200498 : Nat := 4983230072969 + 3 ^ 40 * 200498 * 2
def baseEnd_200498 : Nat := 102951844265261784352933

theorem tailTrace_200498 : CollatzResearch.WordTrace tailWord_200498 prefixEnd_200498 102951844265261784352933 := by
  unfold tailWord_200498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828190706909365794334537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4875175218424975451558765 1828190706909365794334537)
  ·
    refine ⟨1371143030182024345750903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1828190706909365794334537 1371143030182024345750903)
    ·
      refine ⟨2056714545273036518626355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371143030182024345750903 2056714545273036518626355)
      ·
        refine ⟨3085071817909554777939533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056714545273036518626355 3085071817909554777939533)
        ·
          refine ⟨1156901931716083041727325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3085071817909554777939533 1156901931716083041727325)
          ·
            refine ⟨433838224393531140647747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1156901931716083041727325 433838224393531140647747)
            ·
              refine ⟨650757336590296710971621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433838224393531140647747 650757336590296710971621)
              ·
                refine ⟨122017000610680633307179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 650757336590296710971621 122017000610680633307179)
                ·
                  refine ⟨183025500916020949960769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122017000610680633307179 183025500916020949960769)
                  ·
                    refine ⟨137269125687015712470577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183025500916020949960769 137269125687015712470577)
                    ·
                      refine ⟨102951844265261784352933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137269125687015712470577 102951844265261784352933)
                      ·
                        rfl

theorem cell23_200498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_200498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200498 prefixEnd_200498 := by exact prefixLift 200498
  have htrace : WordTrace (prefixWord ++ tailWord_200498) baseStart_200498 baseEnd_200498 := by
    simpa [prefixWord, tailWord_200498, baseEnd_200498] using wordTrace_append hprefix tailTrace_200498
  have hstable : (prefixWord ++ tailWord_200498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200498).length < 2 ^ (prefixWord ++ tailWord_200498).sum := by decide
  have hdescent : baseEnd_200498 < baseStart_200498 := by decide
  rcases family_descends (prefixWord ++ tailWord_200498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200548 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_200548 : Nat := 118140960795 + 200548 * 2 ^ 59
def prefixEnd_200548 : Nat := 4983230072969 + 3 ^ 40 * 200548 * 2
def baseEnd_200548 : Nat := 102977518297986588727703

theorem tailTrace_200548 : CollatzResearch.WordTrace tailWord_200548 prefixEnd_200548 102977518297986588727703 := by
  unfold tailWord_200548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3657293238728160858329149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4876390984970881144438865 3657293238728160858329149)
  ·
    refine ⟨1371484964523060321873431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3657293238728160858329149 1371484964523060321873431)
    ·
      refine ⟨2057227446784590482810147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371484964523060321873431 2057227446784590482810147)
      ·
        refine ⟨3085841170176885724215221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057227446784590482810147 3085841170176885724215221)
        ·
          refine ⟨289297609704083036645177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3085841170176885724215221 289297609704083036645177)
          ·
            refine ⟨216973207278062277483883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289297609704083036645177 216973207278062277483883)
            ·
              refine ⟨325459810917093416225825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216973207278062277483883 325459810917093416225825)
              ·
                refine ⟨244094858187820062169369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325459810917093416225825 244094858187820062169369)
                ·
                  refine ⟨183071143640865046627027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244094858187820062169369 183071143640865046627027)
                  ·
                    refine ⟨274606715461297569940541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 183071143640865046627027 274606715461297569940541)
                    ·
                      refine ⟨102977518297986588727703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 274606715461297569940541 102977518297986588727703)
                      ·
                        rfl

theorem cell23_200548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_200548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200548 prefixEnd_200548 := by exact prefixLift 200548
  have htrace : WordTrace (prefixWord ++ tailWord_200548) baseStart_200548 baseEnd_200548 := by
    simpa [prefixWord, tailWord_200548, baseEnd_200548] using wordTrace_append hprefix tailTrace_200548
  have hstable : (prefixWord ++ tailWord_200548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200548).length < 2 ^ (prefixWord ++ tailWord_200548).sum := by decide
  have hdescent : baseEnd_200548 < baseStart_200548 := by decide
  rcases family_descends (prefixWord ++ tailWord_200548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200557 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_200557 : Nat := 118140960795 + 200557 * 2 ^ 59
def prefixEnd_200557 : Nat := 4983230072969 + 3 ^ 40 * 200557 * 2
def baseEnd_200557 : Nat := 102982139623877053515161

theorem tailTrace_200557 : CollatzResearch.WordTrace tailWord_200557 prefixEnd_200557 102982139623877053515161 := by
  unfold tailWord_200557
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314914734423716253735925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4876609822949144169157283 7314914734423716253735925)
  ·
    refine ⟨685773256352223398787743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7314914734423716253735925 685773256352223398787743)
    ·
      refine ⟨1028659884528335098181615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685773256352223398787743 1028659884528335098181615)
      ·
        refine ⟨1542989826792502647272423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028659884528335098181615 1542989826792502647272423)
        ·
          refine ⟨2314484740188753970908635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542989826792502647272423 2314484740188753970908635)
          ·
            refine ⟨3471727110283130956362953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314484740188753970908635 3471727110283130956362953)
            ·
              refine ⟨2603795332712348217272215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3471727110283130956362953 2603795332712348217272215)
              ·
                refine ⟨3905692999068522325908323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603795332712348217272215 3905692999068522325908323)
                ·
                  refine ⟨5858539498602783488862485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3905692999068522325908323 5858539498602783488862485)
                  ·
                    refine ⟨274619038997005476040429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5858539498602783488862485 274619038997005476040429)
                    ·
                      refine ⟨102982139623877053515161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 274619038997005476040429 102982139623877053515161)
                      ·
                        rfl

theorem cell23_200557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_200557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200557 prefixEnd_200557 := by exact prefixLift 200557
  have htrace : WordTrace (prefixWord ++ tailWord_200557) baseStart_200557 baseEnd_200557 := by
    simpa [prefixWord, tailWord_200557, baseEnd_200557] using wordTrace_append hprefix tailTrace_200557
  have hstable : (prefixWord ++ tailWord_200557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200557).length < 2 ^ (prefixWord ++ tailWord_200557).sum := by decide
  have hdescent : baseEnd_200557 < baseStart_200557 := by decide
  rcases family_descends (prefixWord ++ tailWord_200557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200627 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 4]
def baseStart_200627 : Nat := 118140960795 + 200627 * 2 ^ 59
def prefixEnd_200627 : Nat := 4983230072969 + 3 ^ 40 * 200627 * 2
def baseEnd_200627 : Nat := 103018083269691779639839

theorem tailTrace_200627 : CollatzResearch.WordTrace tailWord_200627 prefixEnd_200627 103018083269691779639839 := by
  unfold tailWord_200627
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317467844170118208784135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4878311896113412139189423 7317467844170118208784135)
  ·
    refine ⟨10976201766255177313176203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7317467844170118208784135 10976201766255177313176203)
    ·
      refine ⟨16464302649382765969764305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10976201766255177313176203 16464302649382765969764305)
      ·
        refine ⟨12348226987037074477323229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16464302649382765969764305 12348226987037074477323229)
        ·
          refine ⟨4630585120138902928996211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12348226987037074477323229 4630585120138902928996211)
          ·
            refine ⟨6945877680208354393494317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4630585120138902928996211 6945877680208354393494317)
            ·
              refine ⟨2604704130078132897560369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6945877680208354393494317 2604704130078132897560369)
              ·
                refine ⟨1953528097558599673170277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604704130078132897560369 1953528097558599673170277)
                ·
                  refine ⟨366286518292237438719427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1953528097558599673170277 366286518292237438719427)
                  ·
                    refine ⟨549429777438356158079141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 366286518292237438719427 549429777438356158079141)
                    ·
                      refine ⟨103018083269691779639839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 549429777438356158079141 103018083269691779639839)
                      ·
                        rfl

theorem cell23_200627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_200627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200627 prefixEnd_200627 := by exact prefixLift 200627
  have htrace : WordTrace (prefixWord ++ tailWord_200627) baseStart_200627 baseEnd_200627 := by
    simpa [prefixWord, tailWord_200627, baseEnd_200627] using wordTrace_append hprefix tailTrace_200627
  have hstable : (prefixWord ++ tailWord_200627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200627).length < 2 ^ (prefixWord ++ tailWord_200627).sum := by decide
  have hdescent : baseEnd_200627 < baseStart_200627 := by decide
  rcases family_descends (prefixWord ++ tailWord_200627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200662 : List Nat := [5, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_200662 : Nat := 118140960795 + 200662 * 2 ^ 59
def prefixEnd_200662 : Nat := 4983230072969 + 3 ^ 40 * 200662 * 2
def baseEnd_200662 : Nat := 11448450565844349189131

theorem tailTrace_200662 : CollatzResearch.WordTrace tailWord_200662 prefixEnd_200662 11448450565844349189131 := by
  unfold tailWord_200662
  simp only [CollatzResearch.WordTrace]
  refine ⟨457421524940207449144265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4879162932695546124205493 457421524940207449144265)
  ·
    refine ⟨343066143705155586858199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 457421524940207449144265 343066143705155586858199)
    ·
      refine ⟨514599215557733380287299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343066143705155586858199 514599215557733380287299)
      ·
        refine ⟨771898823336600070430949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514599215557733380287299 771898823336600070430949)
        ·
          refine ⟨144731029375612513205803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 771898823336600070430949 144731029375612513205803)
          ·
            refine ⟨217096544063418769808705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144731029375612513205803 217096544063418769808705)
            ·
              refine ⟨162822408047564077356529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217096544063418769808705 162822408047564077356529)
              ·
                refine ⟨122116806035673058017397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162822408047564077356529 122116806035673058017397)
                ·
                  refine ⟨11448450565844349189131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122116806035673058017397 11448450565844349189131)
                  ·
                    rfl

theorem cell23_200662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_200662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200662 prefixEnd_200662 := by exact prefixLift 200662
  have htrace : WordTrace (prefixWord ++ tailWord_200662) baseStart_200662 baseEnd_200662 := by
    simpa [prefixWord, tailWord_200662, baseEnd_200662] using wordTrace_append hprefix tailTrace_200662
  have hstable : (prefixWord ++ tailWord_200662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200662).length < 2 ^ (prefixWord ++ tailWord_200662).sum := by decide
  have hdescent : baseEnd_200662 < baseStart_200662 := by decide
  rcases family_descends (prefixWord ++ tailWord_200662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200664 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_200664 : Nat := 118140960795 + 200664 * 2 ^ 59
def prefixEnd_200664 : Nat := 4983230072969 + 3 ^ 40 * 200664 * 2
def baseEnd_200664 : Nat := 103037082053908134877169

theorem tailTrace_200664 : CollatzResearch.WordTrace tailWord_200664 prefixEnd_200664 103037082053908134877169 := by
  unfold tailWord_200664
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659408672518036763940523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4879211563357382351920697 3659408672518036763940523)
  ·
    refine ⟨5489113008777055145910785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3659408672518036763940523 5489113008777055145910785)
    ·
      refine ⟨4116834756582791359433089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5489113008777055145910785 4116834756582791359433089)
      ·
        refine ⟨3087626067437093519574817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4116834756582791359433089 3087626067437093519574817)
        ·
          refine ⟨2315719550577820139681113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3087626067437093519574817 2315719550577820139681113)
          ·
            refine ⟨1736789662933365104760835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315719550577820139681113 1736789662933365104760835)
            ·
              refine ⟨2605184494400047657141253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736789662933365104760835 2605184494400047657141253)
              ·
                refine ⟨488472092700008935713985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2605184494400047657141253 488472092700008935713985)
                ·
                  refine ⟨366354069525006701785489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488472092700008935713985 366354069525006701785489)
                  ·
                    refine ⟨274765552143755026339117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 366354069525006701785489 274765552143755026339117)
                    ·
                      refine ⟨103037082053908134877169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 274765552143755026339117 103037082053908134877169)
                      ·
                        rfl

theorem cell23_200664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_200664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200664 prefixEnd_200664 := by exact prefixLift 200664
  have htrace : WordTrace (prefixWord ++ tailWord_200664) baseStart_200664 baseEnd_200664 := by
    simpa [prefixWord, tailWord_200664, baseEnd_200664] using wordTrace_append hprefix tailTrace_200664
  have hstable : (prefixWord ++ tailWord_200664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200664).length < 2 ^ (prefixWord ++ tailWord_200664).sum := by decide
  have hdescent : baseEnd_200664 < baseStart_200664 := by decide
  rcases family_descends (prefixWord ++ tailWord_200664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200728 : List Nat := [2, 1, 2, 3, 2, 1, 1, 6, 1, 1, 3]
def baseStart_200728 : Nat := 118140960795 + 200728 * 2 ^ 59
def prefixEnd_200728 : Nat := 4983230072969 + 3 ^ 40 * 200728 * 2
def baseEnd_200728 : Nat := 103069944815795884476875

theorem tailTrace_200728 : CollatzResearch.WordTrace tailWord_200728 prefixEnd_200728 103069944815795884476875 := by
  unfold tailWord_200728
  simp only [CollatzResearch.WordTrace]
  refine ⟨3660575808402106229105419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4880767744536141638807225 3660575808402106229105419)
  ·
    refine ⟨5490863712603159343658129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3660575808402106229105419 5490863712603159343658129)
    ·
      refine ⟨4118147784452369507743597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5490863712603159343658129 4118147784452369507743597)
      ·
        refine ⟨1544305419169638565403849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4118147784452369507743597 1544305419169638565403849)
        ·
          refine ⟨1158229064377228924052887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544305419169638565403849 1158229064377228924052887)
          ·
            refine ⟨1737343596565843386079331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158229064377228924052887 1737343596565843386079331)
            ·
              refine ⟨2606015394848765079118997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737343596565843386079331 2606015394848765079118997)
              ·
                refine ⟨122156971633535863083703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2606015394848765079118997 122156971633535863083703)
                ·
                  refine ⟨183235457450303794625555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122156971633535863083703 183235457450303794625555)
                  ·
                    refine ⟨274853186175455691938333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 183235457450303794625555 274853186175455691938333)
                    ·
                      refine ⟨103069944815795884476875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 274853186175455691938333 103069944815795884476875)
                      ·
                        rfl

theorem cell23_200728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_200728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200728 prefixEnd_200728 := by exact prefixLift 200728
  have htrace : WordTrace (prefixWord ++ tailWord_200728) baseStart_200728 baseEnd_200728 := by
    simpa [prefixWord, tailWord_200728, baseEnd_200728] using wordTrace_append hprefix tailTrace_200728
  have hstable : (prefixWord ++ tailWord_200728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200728).length < 2 ^ (prefixWord ++ tailWord_200728).sum := by decide
  have hdescent : baseEnd_200728 < baseStart_200728 := by decide
  rcases family_descends (prefixWord ++ tailWord_200728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200751 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 5, 2, 2]
def baseStart_200751 : Nat := 118140960795 + 200751 * 2 ^ 59
def prefixEnd_200751 : Nat := 4983230072969 + 3 ^ 40 * 200751 * 2
def baseEnd_200751 : Nat := 103081754870849294489269

theorem tailTrace_200751 : CollatzResearch.WordTrace tailWord_200751 prefixEnd_200751 103081754870849294489269 := by
  unfold tailWord_200751
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321990495720887386298107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4881326997147258257532071 7321990495720887386298107)
  ·
    refine ⟨10982985743581331079447161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7321990495720887386298107 10982985743581331079447161)
    ·
      refine ⟨8237239307685998309585371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10982985743581331079447161 8237239307685998309585371)
      ·
        refine ⟨12355858961528997464378057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8237239307685998309585371 12355858961528997464378057)
        ·
          refine ⟨9266894221146748098283543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12355858961528997464378057 9266894221146748098283543)
          ·
            refine ⟨13900341331720122147425315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9266894221146748098283543 13900341331720122147425315)
            ·
              refine ⟨20850511997580183221137973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13900341331720122147425315 20850511997580183221137973)
              ·
                refine ⟨1954735499773142176981685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20850511997580183221137973 1954735499773142176981685)
                ·
                  refine ⟨183256453103732079092033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1954735499773142176981685 183256453103732079092033)
                  ·
                    refine ⟨137442339827799059319025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183256453103732079092033 137442339827799059319025)
                    ·
                      refine ⟨103081754870849294489269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137442339827799059319025 103081754870849294489269)
                      ·
                        rfl

theorem cell23_200751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 2, 2].length) (baseStart_200751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200751 prefixEnd_200751 := by exact prefixLift 200751
  have htrace : WordTrace (prefixWord ++ tailWord_200751) baseStart_200751 baseEnd_200751 := by
    simpa [prefixWord, tailWord_200751, baseEnd_200751] using wordTrace_append hprefix tailTrace_200751
  have hstable : (prefixWord ++ tailWord_200751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200751).length < 2 ^ (prefixWord ++ tailWord_200751).sum := by decide
  have hdescent : baseEnd_200751 < baseStart_200751 := by decide
  rcases family_descends (prefixWord ++ tailWord_200751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200764 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_200764 : Nat := 118140960795 + 200764 * 2 ^ 59
def prefixEnd_200764 : Nat := 4983230072969 + 3 ^ 40 * 200764 * 2
def baseEnd_200764 : Nat := 103088430119357743626709

theorem tailTrace_200764 : CollatzResearch.WordTrace tailWord_200764 prefixEnd_200764 103088430119357743626709 := by
  unfold tailWord_200764
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661232322336895303260673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4881643096449193737680897 3661232322336895303260673)
  ·
    refine ⟨2745924241752671477445505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3661232322336895303260673 2745924241752671477445505)
    ·
      refine ⟨2059443181314503608084129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2745924241752671477445505 2059443181314503608084129)
      ·
        refine ⟨1544582385985877706063097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2059443181314503608084129 1544582385985877706063097)
        ·
          refine ⟨1158436789489408279547323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544582385985877706063097 1158436789489408279547323)
          ·
            refine ⟨1737655184234112419320985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158436789489408279547323 1737655184234112419320985)
            ·
              refine ⟨1303241388175584314490739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737655184234112419320985 1303241388175584314490739)
              ·
                refine ⟨1954862082263376471736109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303241388175584314490739 1954862082263376471736109)
                ·
                  refine ⟨733073280848766176901041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1954862082263376471736109 733073280848766176901041)
                  ·
                    refine ⟨549804960636574632675781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 733073280848766176901041 549804960636574632675781)
                    ·
                      refine ⟨103088430119357743626709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 549804960636574632675781 103088430119357743626709)
                      ·
                        rfl

theorem cell23_200764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_200764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200764 prefixEnd_200764 := by exact prefixLift 200764
  have htrace : WordTrace (prefixWord ++ tailWord_200764) baseStart_200764 baseEnd_200764 := by
    simpa [prefixWord, tailWord_200764, baseEnd_200764] using wordTrace_append hprefix tailTrace_200764
  have hstable : (prefixWord ++ tailWord_200764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200764).length < 2 ^ (prefixWord ++ tailWord_200764).sum := by decide
  have hdescent : baseEnd_200764 < baseStart_200764 := by decide
  rcases family_descends (prefixWord ++ tailWord_200764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200802 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_200802 : Nat := 118140960795 + 200802 * 2 ^ 59
def prefixEnd_200802 : Nat := 4983230072969 + 3 ^ 40 * 200802 * 2
def baseEnd_200802 : Nat := 103107942384228594951535

theorem tailTrace_200802 : CollatzResearch.WordTrace tailWord_200802 prefixEnd_200802 103107942384228594951535 := by
  unfold tailWord_200802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830962654634030774101165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4882567079024082064269773 1830962654634030774101165)
  ·
    refine ⟨686610995487761540287937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1830962654634030774101165 686610995487761540287937)
    ·
      refine ⟨514958246615821155215953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 686610995487761540287937 514958246615821155215953)
      ·
        refine ⟨386218684961865866411965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514958246615821155215953 386218684961865866411965)
        ·
          refine ⟨144832006860699699904487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386218684961865866411965 144832006860699699904487)
          ·
            refine ⟨217248010291049549856731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144832006860699699904487 217248010291049549856731)
            ·
              refine ⟨325872015436574324785097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217248010291049549856731 325872015436574324785097)
              ·
                refine ⟨244404011577430743588823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325872015436574324785097 244404011577430743588823)
                ·
                  refine ⟨366606017366146115383235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244404011577430743588823 366606017366146115383235)
                  ·
                    refine ⟨549909026049219173074853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 366606017366146115383235 549909026049219173074853)
                    ·
                      refine ⟨103107942384228594951535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 549909026049219173074853 103107942384228594951535)
                      ·
                        rfl

theorem cell23_200802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_200802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200802 prefixEnd_200802 := by exact prefixLift 200802
  have htrace : WordTrace (prefixWord ++ tailWord_200802) baseStart_200802 baseEnd_200802 := by
    simpa [prefixWord, tailWord_200802, baseEnd_200802] using wordTrace_append hprefix tailTrace_200802
  have hstable : (prefixWord ++ tailWord_200802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200802).length < 2 ^ (prefixWord ++ tailWord_200802).sum := by decide
  have hdescent : baseEnd_200802 < baseStart_200802 := by decide
  rcases family_descends (prefixWord ++ tailWord_200802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200841 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 3, 4, 2]
def baseStart_200841 : Nat := 118140960795 + 200841 * 2 ^ 59
def prefixEnd_200841 : Nat := 4983230072969 + 3 ^ 40 * 200841 * 2
def baseEnd_200841 : Nat := 103127968129753942363855

theorem tailTrace_200841 : CollatzResearch.WordTrace tailWord_200841 prefixEnd_200841 103127968129753942363855 := by
  unfold tailWord_200841
  simp only [CollatzResearch.WordTrace]
  refine ⟨7325273065394832757074377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4883515376929888504716251 7325273065394832757074377)
  ·
    refine ⟨5493954799046124567805783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7325273065394832757074377 5493954799046124567805783)
    ·
      refine ⟨8240932198569186851708675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493954799046124567805783 8240932198569186851708675)
      ·
        refine ⟨12361398297853780277563013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8240932198569186851708675 12361398297853780277563013)
        ·
          refine ⟨2317762180847583802043065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12361398297853780277563013 2317762180847583802043065)
          ·
            refine ⟨1738321635635687851532299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2317762180847583802043065 1738321635635687851532299)
            ·
              refine ⟨2607482453453531777298449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738321635635687851532299 2607482453453531777298449)
              ·
                refine ⟨1955611840090148832973837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607482453453531777298449 1955611840090148832973837)
                ·
                  refine ⟨733354440033805812365189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1955611840090148832973837 733354440033805812365189)
                  ·
                    refine ⟨137503957506338589818473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 733354440033805812365189 137503957506338589818473)
                    ·
                      refine ⟨103127968129753942363855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137503957506338589818473 103127968129753942363855)
                      ·
                        rfl

theorem cell23_200841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 4, 2].length) (baseStart_200841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200841 prefixEnd_200841 := by exact prefixLift 200841
  have htrace : WordTrace (prefixWord ++ tailWord_200841) baseStart_200841 baseEnd_200841 := by
    simpa [prefixWord, tailWord_200841, baseEnd_200841] using wordTrace_append hprefix tailTrace_200841
  have hstable : (prefixWord ++ tailWord_200841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200841).length < 2 ^ (prefixWord ++ tailWord_200841).sum := by decide
  have hdescent : baseEnd_200841 < baseStart_200841 := by decide
  rcases family_descends (prefixWord ++ tailWord_200841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200864 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 9]
def baseStart_200864 : Nat := 118140960795 + 200864 * 2 ^ 59
def prefixEnd_200864 : Nat := 4983230072969 + 3 ^ 40 * 200864 * 2
def baseEnd_200864 : Nat := 11459975353867483597361

theorem tailTrace_200864 : CollatzResearch.WordTrace tailWord_200864 prefixEnd_200864 11459975353867483597361 := by
  unfold tailWord_200864
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663055972155753842580823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4884074629541005123441097 3663055972155753842580823)
  ·
    refine ⟨5494583958233630763871235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663055972155753842580823 5494583958233630763871235)
    ·
      refine ⟨8241875937350446145806853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5494583958233630763871235 8241875937350446145806853)
      ·
        refine ⟨1545351738253208652338785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8241875937350446145806853 1545351738253208652338785)
        ·
          refine ⟨1159013803689906489254089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1545351738253208652338785 1159013803689906489254089)
          ·
            refine ⟨869260352767429866940567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1159013803689906489254089 869260352767429866940567)
            ·
              refine ⟨1303890529151144800410851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869260352767429866940567 1303890529151144800410851)
              ·
                refine ⟨1955835793726717200616277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303890529151144800410851 1955835793726717200616277)
                ·
                  refine ⟨11459975353867483597361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1955835793726717200616277 11459975353867483597361)
                  ·
                    rfl

theorem cell23_200864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 9].length) (baseStart_200864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200864 prefixEnd_200864 := by exact prefixLift 200864
  have htrace : WordTrace (prefixWord ++ tailWord_200864) baseStart_200864 baseEnd_200864 := by
    simpa [prefixWord, tailWord_200864, baseEnd_200864] using wordTrace_append hprefix tailTrace_200864
  have hstable : (prefixWord ++ tailWord_200864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200864).length < 2 ^ (prefixWord ++ tailWord_200864).sum := by decide
  have hdescent : baseEnd_200864 < baseStart_200864 := by decide
  rcases family_descends (prefixWord ++ tailWord_200864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200901 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 1, 7, 2]
def baseStart_200901 : Nat := 118140960795 + 200901 * 2 ^ 59
def prefixEnd_200901 : Nat := 4983230072969 + 3 ^ 40 * 200901 * 2
def baseEnd_200901 : Nat := 103158776969023707613579

theorem tailTrace_200901 : CollatzResearch.WordTrace tailWord_200901 prefixEnd_200901 103158776969023707613579 := by
  unfold tailWord_200901
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327461445177463004258557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4884974296784975336172371 7327461445177463004258557)
  ·
    refine ⟨2747798041941548626596959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7327461445177463004258557 2747798041941548626596959)
    ·
      refine ⟨4121697062912322939895439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747798041941548626596959 4121697062912322939895439)
      ·
        refine ⟨6182545594368484409843159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121697062912322939895439 6182545594368484409843159)
        ·
          refine ⟨9273818391552726614764739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182545594368484409843159 9273818391552726614764739)
          ·
            refine ⟨13910727587329089922147109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9273818391552726614764739 13910727587329089922147109)
            ·
              refine ⟨2608261422624204360402583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13910727587329089922147109 2608261422624204360402583)
              ·
                refine ⟨3912392133936306540603875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608261422624204360402583 3912392133936306540603875)
                ·
                  refine ⟨5868588200904459810905813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912392133936306540603875 5868588200904459810905813)
                  ·
                    refine ⟨137545035958698276818105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5868588200904459810905813 137545035958698276818105)
                    ·
                      refine ⟨103158776969023707613579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137545035958698276818105 103158776969023707613579)
                      ·
                        rfl

theorem cell23_200901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_200901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200901 prefixEnd_200901 := by exact prefixLift 200901
  have htrace : WordTrace (prefixWord ++ tailWord_200901) baseStart_200901 baseEnd_200901 := by
    simpa [prefixWord, tailWord_200901, baseEnd_200901] using wordTrace_append hprefix tailTrace_200901
  have hstable : (prefixWord ++ tailWord_200901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200901).length < 2 ^ (prefixWord ++ tailWord_200901).sum := by decide
  have hdescent : baseEnd_200901 < baseStart_200901 := by decide
  rcases family_descends (prefixWord ++ tailWord_200901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200904 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_200904 : Nat := 118140960795 + 200904 * 2 ^ 59
def prefixEnd_200904 : Nat := 4983230072969 + 3 ^ 40 * 200904 * 2
def baseEnd_200904 : Nat := 103160317410987195876065

theorem tailTrace_200904 : CollatzResearch.WordTrace tailWord_200904 prefixEnd_200904 103160317410987195876065 := by
  unfold tailWord_200904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663785432083297258308883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4885047242777729677745177 3663785432083297258308883)
  ·
    refine ⟨5495678148124945887463325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663785432083297258308883 5495678148124945887463325)
    ·
      refine ⟨2060879305546854707798747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5495678148124945887463325 2060879305546854707798747)
      ·
        refine ⟨3091318958320282061698121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060879305546854707798747 3091318958320282061698121)
        ·
          refine ⟨2318489218740211546273591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091318958320282061698121 2318489218740211546273591)
          ·
            refine ⟨3477733828110317319410387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318489218740211546273591 3477733828110317319410387)
            ·
              refine ⟨5216600742165475979115581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477733828110317319410387 5216600742165475979115581)
              ·
                refine ⟨1956225278312053492168343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5216600742165475979115581 1956225278312053492168343)
                ·
                  refine ⟨2934337917468080238252515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956225278312053492168343 2934337917468080238252515)
                  ·
                    refine ⟨4401506876202120357378773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2934337917468080238252515 4401506876202120357378773)
                    ·
                      refine ⟨103160317410987195876065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4401506876202120357378773 103160317410987195876065)
                      ·
                        rfl

theorem cell23_200904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_200904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200904 prefixEnd_200904 := by exact prefixLift 200904
  have htrace : WordTrace (prefixWord ++ tailWord_200904) baseStart_200904 baseEnd_200904 := by
    simpa [prefixWord, tailWord_200904, baseEnd_200904] using wordTrace_append hprefix tailTrace_200904
  have hstable : (prefixWord ++ tailWord_200904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200904).length < 2 ^ (prefixWord ++ tailWord_200904).sum := by decide
  have hdescent : baseEnd_200904 < baseStart_200904 := by decide
  rcases family_descends (prefixWord ++ tailWord_200904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200944 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_200944 : Nat := 118140960795 + 200944 * 2 ^ 59
def prefixEnd_200944 : Nat := 4983230072969 + 3 ^ 40 * 200944 * 2
def baseEnd_200944 : Nat := 103180856637167039375881

theorem tailTrace_200944 : CollatzResearch.WordTrace tailWord_200944 prefixEnd_200944 103180856637167039375881 := by
  unfold tailWord_200944
  simp only [CollatzResearch.WordTrace]
  refine ⟨3664514892010840674036943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4886019856014454232049257 3664514892010840674036943)
  ·
    refine ⟨5496772338016261011055415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3664514892010840674036943 5496772338016261011055415)
    ·
      refine ⟨8245158507024391516583123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5496772338016261011055415 8245158507024391516583123)
      ·
        refine ⟨12367737760536587274874685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8245158507024391516583123 12367737760536587274874685)
        ·
          refine ⟨4637901660201220228078007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12367737760536587274874685 4637901660201220228078007)
          ·
            refine ⟨6956852490301830342117011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637901660201220228078007 6956852490301830342117011)
            ·
              refine ⟨10435278735452745513175517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956852490301830342117011 10435278735452745513175517)
              ·
                refine ⟨3913229525794779567440819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10435278735452745513175517 3913229525794779567440819)
                ·
                  refine ⟨5869844288692169351161229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913229525794779567440819 5869844288692169351161229)
                  ·
                    refine ⟨2201191608259563506685461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5869844288692169351161229 2201191608259563506685461)
                    ·
                      refine ⟨103180856637167039375881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2201191608259563506685461 103180856637167039375881)
                      ·
                        rfl

theorem cell23_200944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_200944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200944 prefixEnd_200944 := by exact prefixLift 200944
  have htrace : WordTrace (prefixWord ++ tailWord_200944) baseStart_200944 baseEnd_200944 := by
    simpa [prefixWord, tailWord_200944, baseEnd_200944] using wordTrace_append hprefix tailTrace_200944
  have hstable : (prefixWord ++ tailWord_200944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200944).length < 2 ^ (prefixWord ++ tailWord_200944).sum := by decide
  have hdescent : baseEnd_200944 < baseStart_200944 := by decide
  rcases family_descends (prefixWord ++ tailWord_200944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200971 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 6]
def baseStart_200971 : Nat := 118140960795 + 200971 * 2 ^ 59
def prefixEnd_200971 : Nat := 4983230072969 + 3 ^ 40 * 200971 * 2
def baseEnd_200971 : Nat := 11466080068315381526473

theorem tailTrace_200971 : CollatzResearch.WordTrace tailWord_200971 prefixEnd_200971 11466080068315381526473 := by
  unfold tailWord_200971
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330014554923864959306767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4886676369949243306204511 7330014554923864959306767)
  ·
    refine ⟨10995021832385797438960151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7330014554923864959306767 10995021832385797438960151)
    ·
      refine ⟨16492532748578696158440227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10995021832385797438960151 16492532748578696158440227)
      ·
        refine ⟨24738799122868044237660341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16492532748578696158440227 24738799122868044237660341)
        ·
          refine ⟨2319262417768879147280657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24738799122868044237660341 2319262417768879147280657)
          ·
            refine ⟨1739446813326659360460493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2319262417768879147280657 1739446813326659360460493)
            ·
              refine ⟨652292554997497260172685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1739446813326659360460493 652292554997497260172685)
              ·
                refine ⟨244609708124061472564757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 652292554997497260172685 244609708124061472564757)
                ·
                  refine ⟨11466080068315381526473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 244609708124061472564757 11466080068315381526473)
                  ·
                    rfl

theorem cell23_200971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 6].length) (baseStart_200971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200971 prefixEnd_200971 := by exact prefixLift 200971
  have htrace : WordTrace (prefixWord ++ tailWord_200971) baseStart_200971 baseEnd_200971 := by
    simpa [prefixWord, tailWord_200971, baseEnd_200971] using wordTrace_append hprefix tailTrace_200971
  have hstable : (prefixWord ++ tailWord_200971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200971).length < 2 ^ (prefixWord ++ tailWord_200971).sum := by decide
  have hdescent : baseEnd_200971 < baseStart_200971 := by decide
  rcases family_descends (prefixWord ++ tailWord_200971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200981 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_200981 : Nat := 118140960795 + 200981 * 2 ^ 59
def prefixEnd_200981 : Nat := 4983230072969 + 3 ^ 40 * 200981 * 2
def baseEnd_200981 : Nat := 103199855421383394613211

theorem tailTrace_200981 : CollatzResearch.WordTrace tailWord_200981 prefixEnd_200981 103199855421383394613211 := by
  unfold tailWord_200981
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330379284887636667170797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4886919523258424444780531 7330379284887636667170797)
  ·
    refine ⟨2748892231832863750189049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7330379284887636667170797 2748892231832863750189049)
    ·
      refine ⟨2061669173874647812641787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2748892231832863750189049 2061669173874647812641787)
      ·
        refine ⟨3092503760811971718962681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061669173874647812641787 3092503760811971718962681)
        ·
          refine ⟨2319377820608978789222011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3092503760811971718962681 2319377820608978789222011)
          ·
            refine ⟨3479066730913468183833017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319377820608978789222011 3479066730913468183833017)
            ·
              refine ⟨2609300048185101137874763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3479066730913468183833017 2609300048185101137874763)
              ·
                refine ⟨3913950072277651706812145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2609300048185101137874763 3913950072277651706812145)
                ·
                  refine ⟨2935462554208238780109109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3913950072277651706812145 2935462554208238780109109)
                  ·
                    refine ⟨275199614457022385635229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2935462554208238780109109 275199614457022385635229)
                    ·
                      refine ⟨103199855421383394613211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 275199614457022385635229 103199855421383394613211)
                      ·
                        rfl

theorem cell23_200981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_200981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_200981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_200981 prefixEnd_200981 := by exact prefixLift 200981
  have htrace : WordTrace (prefixWord ++ tailWord_200981) baseStart_200981 baseEnd_200981 := by
    simpa [prefixWord, tailWord_200981, baseEnd_200981] using wordTrace_append hprefix tailTrace_200981
  have hstable : (prefixWord ++ tailWord_200981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200981).length < 2 ^ (prefixWord ++ tailWord_200981).sum := by decide
  have hdescent : baseEnd_200981 < baseStart_200981 := by decide
  rcases family_descends (prefixWord ++ tailWord_200981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201008 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 4, 3, 2]
def baseStart_201008 : Nat := 118140960795 + 201008 * 2 ^ 59
def prefixEnd_201008 : Nat := 4983230072969 + 3 ^ 40 * 201008 * 2
def baseEnd_201008 : Nat := 103213719399054788975587

theorem tailTrace_201008 : CollatzResearch.WordTrace tailWord_201008 prefixEnd_201008 103213719399054788975587 := by
  unfold tailWord_201008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3665682027894910139201839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4887576037193213518935785 3665682027894910139201839)
  ·
    refine ⟨5498523041842365208802759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3665682027894910139201839 5498523041842365208802759)
    ·
      refine ⟨8247784562763547813204139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5498523041842365208802759 8247784562763547813204139)
      ·
        refine ⟨12371676844145321719806209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8247784562763547813204139 12371676844145321719806209)
        ·
          refine ⟨9278757633108991289854657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12371676844145321719806209 9278757633108991289854657)
          ·
            refine ⟨6959068224831743467390993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9278757633108991289854657 6959068224831743467390993)
            ·
              refine ⟨5219301168623807600543245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6959068224831743467390993 5219301168623807600543245)
              ·
                refine ⟨1957237938233927850203717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5219301168623807600543245 1957237938233927850203717)
                ·
                  refine ⟨366982113418861471913197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957237938233927850203717 366982113418861471913197)
                  ·
                    refine ⟨137618292532073051967449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 366982113418861471913197 137618292532073051967449)
                    ·
                      refine ⟨103213719399054788975587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137618292532073051967449 103213719399054788975587)
                      ·
                        rfl

theorem cell23_201008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 3, 2].length) (baseStart_201008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201008 prefixEnd_201008 := by exact prefixLift 201008
  have htrace : WordTrace (prefixWord ++ tailWord_201008) baseStart_201008 baseEnd_201008 := by
    simpa [prefixWord, tailWord_201008, baseEnd_201008] using wordTrace_append hprefix tailTrace_201008
  have hstable : (prefixWord ++ tailWord_201008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201008).length < 2 ^ (prefixWord ++ tailWord_201008).sum := by decide
  have hdescent : baseEnd_201008 < baseStart_201008 := by decide
  rcases family_descends (prefixWord ++ tailWord_201008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201009 : List Nat := [1, 2, 2, 3, 4, 2, 2, 2, 1, 4]
def baseStart_201009 : Nat := 118140960795 + 201009 * 2 ^ 59
def prefixEnd_201009 : Nat := 4983230072969 + 3 ^ 40 * 201009 * 2
def baseEnd_201009 : Nat := 34404744293236428354361

theorem tailTrace_201009 : CollatzResearch.WordTrace tailWord_201009 prefixEnd_201009 34404744293236428354361 := by
  unfold tailWord_201009
  simp only [CollatzResearch.WordTrace]
  refine ⟨7331400528786197449190081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4887600352524131632793387 7331400528786197449190081)
  ·
    refine ⟨5498550396589648086892561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7331400528786197449190081 5498550396589648086892561)
    ·
      refine ⟨4123912797442236065169421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5498550396589648086892561 4123912797442236065169421)
      ·
        refine ⟨1546467299040838524438533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4123912797442236065169421 1546467299040838524438533)
        ·
          refine ⟨289962618570157223332225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1546467299040838524438533 289962618570157223332225)
          ·
            refine ⟨217471963927617917499169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289962618570157223332225 217471963927617917499169)
            ·
              refine ⟨163103972945713438124377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217471963927617917499169 163103972945713438124377)
              ·
                refine ⟨122327979709285078593283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163103972945713438124377 122327979709285078593283)
                ·
                  refine ⟨183491969563927617889925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122327979709285078593283 183491969563927617889925)
                  ·
                    refine ⟨34404744293236428354361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 183491969563927617889925 34404744293236428354361)
                    ·
                      rfl

theorem cell23_201009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_201009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201009 prefixEnd_201009 := by exact prefixLift 201009
  have htrace : WordTrace (prefixWord ++ tailWord_201009) baseStart_201009 baseEnd_201009 := by
    simpa [prefixWord, tailWord_201009, baseEnd_201009] using wordTrace_append hprefix tailTrace_201009
  have hstable : (prefixWord ++ tailWord_201009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201009).length < 2 ^ (prefixWord ++ tailWord_201009).sum := by decide
  have hdescent : baseEnd_201009 < baseStart_201009 := by decide
  rcases family_descends (prefixWord ++ tailWord_201009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201038 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_201038 : Nat := 118140960795 + 201038 * 2 ^ 59
def prefixEnd_201038 : Nat := 4983230072969 + 3 ^ 40 * 201038 * 2
def baseEnd_201038 : Nat := 103229123818689671600449

theorem tailTrace_201038 : CollatzResearch.WordTrace tailWord_201038 prefixEnd_201038 103229123818689671600449 := by
  unfold tailWord_201038
  simp only [CollatzResearch.WordTrace]
  refine ⟨916557280710141925249471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4888305497120756934663845 916557280710141925249471)
  ·
    refine ⟨1374835921065212887874207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 916557280710141925249471 1374835921065212887874207)
    ·
      refine ⟨2062253881597819331811311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1374835921065212887874207 2062253881597819331811311)
      ·
        refine ⟨3093380822396728997716967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062253881597819331811311 3093380822396728997716967)
        ·
          refine ⟨4640071233595093496575451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3093380822396728997716967 4640071233595093496575451)
          ·
            refine ⟨6960106850392640244863177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640071233595093496575451 6960106850392640244863177)
            ·
              refine ⟨5220080137794480183647383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6960106850392640244863177 5220080137794480183647383)
              ·
                refine ⟨7830120206691720275471075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220080137794480183647383 7830120206691720275471075)
                ·
                  refine ⟨11745180310037580413206613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7830120206691720275471075 11745180310037580413206613)
                  ·
                    refine ⟨137638831758252895467265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11745180310037580413206613 137638831758252895467265)
                    ·
                      refine ⟨103229123818689671600449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137638831758252895467265 103229123818689671600449)
                      ·
                        rfl

theorem cell23_201038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_201038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201038 prefixEnd_201038 := by exact prefixLift 201038
  have htrace : WordTrace (prefixWord ++ tailWord_201038) baseStart_201038 baseEnd_201038 := by
    simpa [prefixWord, tailWord_201038, baseEnd_201038] using wordTrace_append hprefix tailTrace_201038
  have hstable : (prefixWord ++ tailWord_201038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201038).length < 2 ^ (prefixWord ++ tailWord_201038).sum := by decide
  have hdescent : baseEnd_201038 < baseStart_201038 := by decide
  rcases family_descends (prefixWord ++ tailWord_201038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201052 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_201052 : Nat := 118140960795 + 201052 * 2 ^ 59
def prefixEnd_201052 : Nat := 4983230072969 + 3 ^ 40 * 201052 * 2
def baseEnd_201052 : Nat := 34412104182617538941795

theorem tailTrace_201052 : CollatzResearch.WordTrace tailWord_201052 prefixEnd_201052 34412104182617538941795 := by
  unfold tailWord_201052
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666484433815207896502705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4888645911753610528670273 3666484433815207896502705)
  ·
    refine ⟨2749863325361405922377029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3666484433815207896502705 2749863325361405922377029)
    ·
      refine ⟨515599373505263610445693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2749863325361405922377029 515599373505263610445693)
      ·
        refine ⟨193349765064473853917135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515599373505263610445693 193349765064473853917135)
        ·
          refine ⟨290024647596710780875703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193349765064473853917135 290024647596710780875703)
          ·
            refine ⟨435036971395066171313555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290024647596710780875703 435036971395066171313555)
            ·
              refine ⟨652555457092599256970333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435036971395066171313555 652555457092599256970333)
              ·
                refine ⟨244708296409724721363875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 652555457092599256970333 244708296409724721363875)
                ·
                  refine ⟨367062444614587082045813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244708296409724721363875 367062444614587082045813)
                  ·
                    refine ⟨34412104182617538941795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 367062444614587082045813 34412104182617538941795)
                    ·
                      rfl

theorem cell23_201052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_201052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201052 prefixEnd_201052 := by exact prefixLift 201052
  have htrace : WordTrace (prefixWord ++ tailWord_201052) baseStart_201052 baseEnd_201052 := by
    simpa [prefixWord, tailWord_201052, baseEnd_201052] using wordTrace_append hprefix tailTrace_201052
  have hstable : (prefixWord ++ tailWord_201052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201052).length < 2 ^ (prefixWord ++ tailWord_201052).sum := by decide
  have hdescent : baseEnd_201052 < baseStart_201052 := by decide
  rcases family_descends (prefixWord ++ tailWord_201052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201055 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 1, 1, 4]
def baseStart_201055 : Nat := 118140960795 + 201055 * 2 ^ 59
def prefixEnd_201055 : Nat := 4983230072969 + 3 ^ 40 * 201055 * 2
def baseEnd_201055 : Nat := 103237852989816105087871

theorem tailTrace_201055 : CollatzResearch.WordTrace tailWord_201055 prefixEnd_201055 103237852989816105087871 := by
  unfold tailWord_201055
  simp only [CollatzResearch.WordTrace]
  refine ⟨7333078286619547305364619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4888718857746364870243079 7333078286619547305364619)
  ·
    refine ⟨10999617429929320958046929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7333078286619547305364619 10999617429929320958046929)
    ·
      refine ⟨8249713072446990718535197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10999617429929320958046929 8249713072446990718535197)
      ·
        refine ⟨3093642402167621519450699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8249713072446990718535197 3093642402167621519450699)
        ·
          refine ⟨4640463603251432279176049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3093642402167621519450699 4640463603251432279176049)
          ·
            refine ⟨3480347702438574209382037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4640463603251432279176049 3480347702438574209382037)
            ·
              refine ⟨163141298551808166064783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3480347702438574209382037 163141298551808166064783)
              ·
                refine ⟨244711947827712249097175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163141298551808166064783 244711947827712249097175)
                ·
                  refine ⟨367067921741568373645763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244711947827712249097175 367067921741568373645763)
                  ·
                    refine ⟨550601882612352560468645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 367067921741568373645763 550601882612352560468645)
                    ·
                      refine ⟨103237852989816105087871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 550601882612352560468645 103237852989816105087871)
                      ·
                        rfl

theorem cell23_201055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_201055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201055 prefixEnd_201055 := by exact prefixLift 201055
  have htrace : WordTrace (prefixWord ++ tailWord_201055) baseStart_201055 baseEnd_201055 := by
    simpa [prefixWord, tailWord_201055, baseEnd_201055] using wordTrace_append hprefix tailTrace_201055
  have hstable : (prefixWord ++ tailWord_201055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201055).length < 2 ^ (prefixWord ++ tailWord_201055).sum := by decide
  have hdescent : baseEnd_201055 < baseStart_201055 := by decide
  rcases family_descends (prefixWord ++ tailWord_201055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201061 : List Nat := [1, 3, 1, 3, 1, 4, 10]
def baseStart_201061 : Nat := 118140960795 + 201061 * 2 ^ 59
def prefixEnd_201061 : Nat := 4983230072969 + 3 ^ 40 * 201061 * 2
def baseEnd_201061 : Nat := 1274579430540038044603

theorem tailTrace_201061 : CollatzResearch.WordTrace tailWord_201061 prefixEnd_201061 1274579430540038044603 := by
  unfold tailWord_201061
  simp only [CollatzResearch.WordTrace]
  refine ⟨7333297124597810330083037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4888864749731873553388691 7333297124597810330083037)
  ·
    refine ⟨2749986421724178873781139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7333297124597810330083037 2749986421724178873781139)
    ·
      refine ⟨4124979632586268310671709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2749986421724178873781139 4124979632586268310671709)
      ·
        refine ⟨1546867362219850616501891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4124979632586268310671709 1546867362219850616501891)
        ·
          refine ⟨2320301043329775924752837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546867362219850616501891 2320301043329775924752837)
          ·
            refine ⟨435056445624332985891157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2320301043329775924752837 435056445624332985891157)
            ·
              refine ⟨1274579430540038044603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 435056445624332985891157 1274579430540038044603)
              ·
                rfl

theorem cell23_201061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 10].length) (baseStart_201061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201061 prefixEnd_201061 := by exact prefixLift 201061
  have htrace : WordTrace (prefixWord ++ tailWord_201061) baseStart_201061 baseEnd_201061 := by
    simpa [prefixWord, tailWord_201061, baseEnd_201061] using wordTrace_append hprefix tailTrace_201061
  have hstable : (prefixWord ++ tailWord_201061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201061).length < 2 ^ (prefixWord ++ tailWord_201061).sum := by decide
  have hdescent : baseEnd_201061 < baseStart_201061 := by decide
  rcases family_descends (prefixWord ++ tailWord_201061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201072 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 3, 2, 2]
def baseStart_201072 : Nat := 118140960795 + 201072 * 2 ^ 59
def prefixEnd_201072 : Nat := 4983230072969 + 3 ^ 40 * 201072 * 2
def baseEnd_201072 : Nat := 103246582160942538575293

theorem tailTrace_201072 : CollatzResearch.WordTrace tailWord_201072 prefixEnd_201072 103246582160942538575293 := by
  unfold tailWord_201072
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666849163778979604366735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4889132218371972805822313 3666849163778979604366735)
  ·
    refine ⟨5500273745668469406550103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3666849163778979604366735 5500273745668469406550103)
    ·
      refine ⟨8250410618502704109825155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5500273745668469406550103 8250410618502704109825155)
      ·
        refine ⟨12375615927754056164737733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8250410618502704109825155 12375615927754056164737733)
        ·
          refine ⟨2320427986453885530888325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12375615927754056164737733 2320427986453885530888325)
          ·
            refine ⟨435080247460103537041561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2320427986453885530888325 435080247460103537041561)
            ·
              refine ⟨326310185595077652781171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435080247460103537041561 326310185595077652781171)
              ·
                refine ⟨489465278392616479171757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326310185595077652781171 489465278392616479171757)
                ·
                  refine ⟨183549479397231179689409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489465278392616479171757 183549479397231179689409)
                  ·
                    refine ⟨137662109547923384767057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183549479397231179689409 137662109547923384767057)
                    ·
                      refine ⟨103246582160942538575293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137662109547923384767057 103246582160942538575293)
                      ·
                        rfl

theorem cell23_201072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 2, 2].length) (baseStart_201072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201072 prefixEnd_201072 := by exact prefixLift 201072
  have htrace : WordTrace (prefixWord ++ tailWord_201072) baseStart_201072 baseEnd_201072 := by
    simpa [prefixWord, tailWord_201072, baseEnd_201072] using wordTrace_append hprefix tailTrace_201072
  have hstable : (prefixWord ++ tailWord_201072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201072).length < 2 ^ (prefixWord ++ tailWord_201072).sum := by decide
  have hdescent : baseEnd_201072 < baseStart_201072 := by decide
  rcases family_descends (prefixWord ++ tailWord_201072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201085 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_201085 : Nat := 118140960795 + 201085 * 2 ^ 59
def prefixEnd_201085 : Nat := 4983230072969 + 3 ^ 40 * 201085 * 2
def baseEnd_201085 : Nat := 103253257409450987712733

theorem tailTrace_201085 : CollatzResearch.WordTrace tailWord_201085 prefixEnd_201085 103253257409450987712733 := by
  unfold tailWord_201085
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334172476510862428956709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4889448317673908285971139 7334172476510862428956709)
  ·
    refine ⟨1375157339345786705429383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7334172476510862428956709 1375157339345786705429383)
    ·
      refine ⟨2062736009018680058144075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1375157339345786705429383 2062736009018680058144075)
      ·
        refine ⟨3094104013528020087216113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062736009018680058144075 3094104013528020087216113)
        ·
          refine ⟨2320578010146015065412085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3094104013528020087216113 2320578010146015065412085)
          ·
            refine ⟨217554188451188912382383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2320578010146015065412085 217554188451188912382383)
            ·
              refine ⟨326331282676783368573575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217554188451188912382383 326331282676783368573575)
              ·
                refine ⟨489496924015175052860363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326331282676783368573575 489496924015175052860363)
                ·
                  refine ⟨734245386022762579290545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489496924015175052860363 734245386022762579290545)
                  ·
                    refine ⟨550684039517071934467909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 734245386022762579290545 550684039517071934467909)
                    ·
                      refine ⟨103253257409450987712733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 550684039517071934467909 103253257409450987712733)
                      ·
                        rfl

theorem cell23_201085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_201085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201085 prefixEnd_201085 := by exact prefixLift 201085
  have htrace : WordTrace (prefixWord ++ tailWord_201085) baseStart_201085 baseEnd_201085 := by
    simpa [prefixWord, tailWord_201085, baseEnd_201085] using wordTrace_append hprefix tailTrace_201085
  have hstable : (prefixWord ++ tailWord_201085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201085).length < 2 ^ (prefixWord ++ tailWord_201085).sum := by decide
  have hdescent : baseEnd_201085 < baseStart_201085 := by decide
  rcases family_descends (prefixWord ++ tailWord_201085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201122 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_201122 : Nat := 118140960795 + 201122 * 2 ^ 59
def prefixEnd_201122 : Nat := 4983230072969 + 3 ^ 40 * 201122 * 2
def baseEnd_201122 : Nat := 103272256193667342950063

theorem tailTrace_201122 : CollatzResearch.WordTrace tailWord_201122 prefixEnd_201122 103272256193667342950063 := by
  unfold tailWord_201122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833880494344204437013405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4890347984917878498702413 1833880494344204437013405)
  ·
    refine ⟨687705185379076663880027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1833880494344204437013405 687705185379076663880027)
    ·
      refine ⟨1031557778068614995820041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687705185379076663880027 1031557778068614995820041)
      ·
        refine ⟨773668333551461246865031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1031557778068614995820041 773668333551461246865031)
        ·
          refine ⟨1160502500327191870297547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773668333551461246865031 1160502500327191870297547)
          ·
            refine ⟨1740753750490787805446321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160502500327191870297547 1740753750490787805446321)
            ·
              refine ⟨1305565312868090854084741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740753750490787805446321 1305565312868090854084741)
              ·
                refine ⟨244793496162767035140889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1305565312868090854084741 244793496162767035140889)
                ·
                  refine ⟨183595122122075276355667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244793496162767035140889 183595122122075276355667)
                  ·
                    refine ⟨275392683183112914533501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 183595122122075276355667 275392683183112914533501)
                    ·
                      refine ⟨103272256193667342950063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 275392683183112914533501 103272256193667342950063)
                      ·
                        rfl

theorem cell23_201122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_201122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201122 prefixEnd_201122 := by exact prefixLift 201122
  have htrace : WordTrace (prefixWord ++ tailWord_201122) baseStart_201122 baseEnd_201122 := by
    simpa [prefixWord, tailWord_201122, baseEnd_201122] using wordTrace_append hprefix tailTrace_201122
  have hstable : (prefixWord ++ tailWord_201122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201122).length < 2 ^ (prefixWord ++ tailWord_201122).sum := by decide
  have hdescent : baseEnd_201122 < baseStart_201122 := by decide
  rcases family_descends (prefixWord ++ tailWord_201122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201149 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_201149 : Nat := 118140960795 + 201149 * 2 ^ 59
def prefixEnd_201149 : Nat := 4983230072969 + 3 ^ 40 * 201149 * 2
def baseEnd_201149 : Nat := 103286120171338737312439

theorem tailTrace_201149 : CollatzResearch.WordTrace tailWord_201149 prefixEnd_201149 103286120171338737312439 := by
  unfold tailWord_201149
  simp only [CollatzResearch.WordTrace]
  refine ⟨7336506748279001359286501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4891004498852667572857667 7336506748279001359286501)
  ·
    refine ⟨1375595015302312754866219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7336506748279001359286501 1375595015302312754866219)
    ·
      refine ⟨2063392522953469132299329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1375595015302312754866219 2063392522953469132299329)
      ·
        refine ⟨1547544392215101849224497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2063392522953469132299329 1547544392215101849224497)
        ·
          refine ⟨1160658294161326386918373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1547544392215101849224497 1160658294161326386918373)
          ·
            refine ⟨217623430155248697547195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1160658294161326386918373 217623430155248697547195)
            ·
              refine ⟨326435145232873046320793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217623430155248697547195 326435145232873046320793)
              ·
                refine ⟨244826358924654784740595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326435145232873046320793 244826358924654784740595)
                ·
                  refine ⟨367239538386982177110893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244826358924654784740595 367239538386982177110893)
                  ·
                    refine ⟨137714826895118316416585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367239538386982177110893 137714826895118316416585)
                    ·
                      refine ⟨103286120171338737312439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137714826895118316416585 103286120171338737312439)
                      ·
                        rfl

theorem cell23_201149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_201149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201149 prefixEnd_201149 := by exact prefixLift 201149
  have htrace : WordTrace (prefixWord ++ tailWord_201149) baseStart_201149 baseEnd_201149 := by
    simpa [prefixWord, tailWord_201149, baseEnd_201149] using wordTrace_append hprefix tailTrace_201149
  have hstable : (prefixWord ++ tailWord_201149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201149).length < 2 ^ (prefixWord ++ tailWord_201149).sum := by decide
  have hdescent : baseEnd_201149 < baseStart_201149 := by decide
  rcases family_descends (prefixWord ++ tailWord_201149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201171 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 8]
def baseStart_201171 : Nat := 118140960795 + 201171 * 2 ^ 59
def prefixEnd_201171 : Nat := 4983230072969 + 3 ^ 40 * 201171 * 2
def baseEnd_201171 : Nat := 103297416745737651237337

theorem tailTrace_201171 : CollatzResearch.WordTrace tailWord_201171 prefixEnd_201171 103297416745737651237337 := by
  unfold tailWord_201171
  simp only [CollatzResearch.WordTrace]
  refine ⟨7337309154199299116587367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4891539436132866077724911 7337309154199299116587367)
  ·
    refine ⟨11005963731298948674881051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7337309154199299116587367 11005963731298948674881051)
    ·
      refine ⟨16508945596948423012321577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11005963731298948674881051 16508945596948423012321577)
      ·
        refine ⟨12381709197711317259241183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16508945596948423012321577 12381709197711317259241183)
        ·
          refine ⟨18572563796566975888861775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12381709197711317259241183 18572563796566975888861775)
          ·
            refine ⟨27858845694850463833292663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18572563796566975888861775 27858845694850463833292663)
            ·
              refine ⟨41788268542275695749938995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27858845694850463833292663 41788268542275695749938995)
              ·
                refine ⟨62682402813413543624908493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41788268542275695749938995 62682402813413543624908493)
                ·
                  refine ⟨23505901055030078859340685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62682402813413543624908493 23505901055030078859340685)
                  ·
                    refine ⟨8814712895636279572252757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23505901055030078859340685 8814712895636279572252757)
                    ·
                      refine ⟨103297416745737651237337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 8814712895636279572252757 103297416745737651237337)
                      ·
                        rfl

theorem cell23_201171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_201171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201171 prefixEnd_201171 := by exact prefixLift 201171
  have htrace : WordTrace (prefixWord ++ tailWord_201171) baseStart_201171 baseEnd_201171 := by
    simpa [prefixWord, tailWord_201171, baseEnd_201171] using wordTrace_append hprefix tailTrace_201171
  have hstable : (prefixWord ++ tailWord_201171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201171).length < 2 ^ (prefixWord ++ tailWord_201171).sum := by decide
  have hdescent : baseEnd_201171 < baseStart_201171 := by decide
  rcases family_descends (prefixWord ++ tailWord_201171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201185 : List Nat := [1, 2, 3, 1, 2, 2, 3, 4, 5]
def baseStart_201185 : Nat := 118140960795 + 201185 * 2 ^ 59
def prefixEnd_201185 : Nat := 4983230072969 + 3 ^ 40 * 201185 * 2
def baseEnd_201185 : Nat := 11478289497211177384697

theorem tailTrace_201185 : CollatzResearch.WordTrace tailWord_201185 prefixEnd_201185 11478289497211177384697 := by
  unfold tailWord_201185
  simp only [CollatzResearch.WordTrace]
  refine ⟨7337819776148579507597009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4891879850765719671731339 7337819776148579507597009)
  ·
    refine ⟨5503364832111434630697757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7337819776148579507597009 5503364832111434630697757)
    ·
      refine ⟨2063761812041787986511659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5503364832111434630697757 2063761812041787986511659)
      ·
        refine ⟨3095642718062681979767489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063761812041787986511659 3095642718062681979767489)
        ·
          refine ⟨2321732038547011484825617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3095642718062681979767489 2321732038547011484825617)
          ·
            refine ⟨1741299028910258613619213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2321732038547011484825617 1741299028910258613619213)
            ·
              refine ⟨652987135841346980107205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1741299028910258613619213 652987135841346980107205)
              ·
                refine ⟨122435087970252558770101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 652987135841346980107205 122435087970252558770101)
                ·
                  refine ⟨11478289497211177384697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122435087970252558770101 11478289497211177384697)
                  ·
                    rfl

theorem cell23_201185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 5].length) (baseStart_201185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201185 prefixEnd_201185 := by exact prefixLift 201185
  have htrace : WordTrace (prefixWord ++ tailWord_201185) baseStart_201185 baseEnd_201185 := by
    simpa [prefixWord, tailWord_201185, baseEnd_201185] using wordTrace_append hprefix tailTrace_201185
  have hstable : (prefixWord ++ tailWord_201185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201185).length < 2 ^ (prefixWord ++ tailWord_201185).sum := by decide
  have hdescent : baseEnd_201185 < baseStart_201185 := by decide
  rcases family_descends (prefixWord ++ tailWord_201185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201229 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_201229 : Nat := 118140960795 + 201229 * 2 ^ 59
def prefixEnd_201229 : Nat := 4983230072969 + 3 ^ 40 * 201229 * 2
def baseEnd_201229 : Nat := 103327198623698424312071

theorem tailTrace_201229 : CollatzResearch.WordTrace tailWord_201229 prefixEnd_201229 103327198623698424312071 := by
  unfold tailWord_201229
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339424587989175022198741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4892949725326116681465827 7339424587989175022198741)
  ·
    refine ⟨172017763780996289582783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7339424587989175022198741 172017763780996289582783)
    ·
      refine ⟨258026645671494434374175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172017763780996289582783 258026645671494434374175)
      ·
        refine ⟨387039968507241651561263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258026645671494434374175 387039968507241651561263)
        ·
          refine ⟨580559952760862477341895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387039968507241651561263 580559952760862477341895)
          ·
            refine ⟨870839929141293716012843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580559952760862477341895 870839929141293716012843)
            ·
              refine ⟨1306259893711940574019265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870839929141293716012843 1306259893711940574019265)
              ·
                refine ⟨979694920283955430514449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306259893711940574019265 979694920283955430514449)
                ·
                  refine ⟨734771190212966572885837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 979694920283955430514449 734771190212966572885837)
                  ·
                    refine ⟨275539196329862464832189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734771190212966572885837 275539196329862464832189)
                    ·
                      refine ⟨103327198623698424312071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 275539196329862464832189 103327198623698424312071)
                      ·
                        rfl

theorem cell23_201229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_201229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201229 prefixEnd_201229 := by exact prefixLift 201229
  have htrace : WordTrace (prefixWord ++ tailWord_201229) baseStart_201229 baseEnd_201229 := by
    simpa [prefixWord, tailWord_201229, baseEnd_201229] using wordTrace_append hprefix tailTrace_201229
  have hstable : (prefixWord ++ tailWord_201229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201229).length < 2 ^ (prefixWord ++ tailWord_201229).sum := by decide
  have hdescent : baseEnd_201229 < baseStart_201229 := by decide
  rcases family_descends (prefixWord ++ tailWord_201229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201235 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 4, 4, 2]
def baseStart_201235 : Nat := 118140960795 + 201235 * 2 ^ 59
def prefixEnd_201235 : Nat := 4983230072969 + 3 ^ 40 * 201235 * 2
def baseEnd_201235 : Nat := 103330279507625400837043

theorem tailTrace_201235 : CollatzResearch.WordTrace tailWord_201235 prefixEnd_201235 103330279507625400837043 := by
  unfold tailWord_201235
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339643425967438046917159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4893095617311625364611439 7339643425967438046917159)
  ·
    refine ⟨11009465138951157070375739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7339643425967438046917159 11009465138951157070375739)
    ·
      refine ⟨16514197708426735605563609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11009465138951157070375739 16514197708426735605563609)
      ·
        refine ⟨12385648281320051704172707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16514197708426735605563609 12385648281320051704172707)
        ·
          refine ⟨18578472421980077556259061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12385648281320051704172707 18578472421980077556259061)
          ·
            refine ⟨1741731789560632270899287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18578472421980077556259061 1741731789560632270899287)
            ·
              refine ⟨2612597684340948406348931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741731789560632270899287 2612597684340948406348931)
              ·
                refine ⟨3918896526511422609523397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612597684340948406348931 3918896526511422609523397)
                ·
                  refine ⟨734793098720891739285637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3918896526511422609523397 734793098720891739285637)
                  ·
                    refine ⟨137773706010167201116057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734793098720891739285637 137773706010167201116057)
                    ·
                      refine ⟨103330279507625400837043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137773706010167201116057 103330279507625400837043)
                      ·
                        rfl

theorem cell23_201235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 4, 2].length) (baseStart_201235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201235 prefixEnd_201235 := by exact prefixLift 201235
  have htrace : WordTrace (prefixWord ++ tailWord_201235) baseStart_201235 baseEnd_201235 := by
    simpa [prefixWord, tailWord_201235, baseEnd_201235] using wordTrace_append hprefix tailTrace_201235
  have hstable : (prefixWord ++ tailWord_201235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201235).length < 2 ^ (prefixWord ++ tailWord_201235).sum := by decide
  have hdescent : baseEnd_201235 < baseStart_201235 := by decide
  rcases family_descends (prefixWord ++ tailWord_201235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201335 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 6, 4]
def baseStart_201335 : Nat := 118140960795 + 201335 * 2 ^ 59
def prefixEnd_201335 : Nat := 4983230072969 + 3 ^ 40 * 201335 * 2
def baseEnd_201335 : Nat := 34460542524358336528861

theorem tailTrace_201335 : CollatzResearch.WordTrace tailWord_201335 prefixEnd_201335 34460542524358336528861 := by
  unfold tailWord_201335
  simp only [CollatzResearch.WordTrace]
  refine ⟨7343290725605155125557459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4895527150403436750371639 7343290725605155125557459)
  ·
    refine ⟨11014936088407732688336189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7343290725605155125557459 11014936088407732688336189)
    ·
      refine ⟨4130601033152899758126071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11014936088407732688336189 4130601033152899758126071)
      ·
        refine ⟨6195901549729349637189107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130601033152899758126071 6195901549729349637189107)
        ·
          refine ⟨9293852324594024455783661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6195901549729349637189107 9293852324594024455783661)
          ·
            refine ⟨3485194621722759170918873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9293852324594024455783661 3485194621722759170918873)
            ·
              refine ⟨2613895966292069378189155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3485194621722759170918873 2613895966292069378189155)
              ·
                refine ⟨3920843949438104067283733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613895966292069378189155 3920843949438104067283733)
                ·
                  refine ⟨183789560129911128153925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3920843949438104067283733 183789560129911128153925)
                  ·
                    refine ⟨34460542524358336528861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 183789560129911128153925 34460542524358336528861)
                    ·
                      rfl

theorem cell23_201335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_201335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201335 prefixEnd_201335 := by exact prefixLift 201335
  have htrace : WordTrace (prefixWord ++ tailWord_201335) baseStart_201335 baseEnd_201335 := by
    simpa [prefixWord, tailWord_201335, baseEnd_201335] using wordTrace_append hprefix tailTrace_201335
  have hstable : (prefixWord ++ tailWord_201335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201335).length < 2 ^ (prefixWord ++ tailWord_201335).sum := by decide
  have hdescent : baseEnd_201335 < baseStart_201335 := by decide
  rcases family_descends (prefixWord ++ tailWord_201335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201372 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_201372 : Nat := 118140960795 + 201372 * 2 ^ 59
def prefixEnd_201372 : Nat := 4983230072969 + 3 ^ 40 * 201372 * 2
def baseEnd_201372 : Nat := 103400626357291364823913

theorem tailTrace_201372 : CollatzResearch.WordTrace tailWord_201372 prefixEnd_201372 103400626357291364823913 := by
  unfold tailWord_201372
  simp only [CollatzResearch.WordTrace]
  refine ⟨3672320113235555222327185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4896426817647406963102913 3672320113235555222327185)
  ·
    refine ⟨2754240084926666416745389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3672320113235555222327185 2754240084926666416745389)
    ·
      refine ⟨1032840031847499906279521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2754240084926666416745389 1032840031847499906279521)
      ·
        refine ⟨774630023885624929709641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1032840031847499906279521 774630023885624929709641)
        ·
          refine ⟨580972517914218697282231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774630023885624929709641 580972517914218697282231)
          ·
            refine ⟨871458776871328045923347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580972517914218697282231 871458776871328045923347)
            ·
              refine ⟨1307188165306992068885021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871458776871328045923347 1307188165306992068885021)
              ·
                refine ⟨490195561990122025831883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1307188165306992068885021 490195561990122025831883)
                ·
                  refine ⟨735293342985183038747825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490195561990122025831883 735293342985183038747825)
                  ·
                    refine ⟨551470007238887279060869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735293342985183038747825 551470007238887279060869)
                    ·
                      refine ⟨103400626357291364823913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 551470007238887279060869 103400626357291364823913)
                      ·
                        rfl

theorem cell23_201372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_201372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201372 prefixEnd_201372 := by exact prefixLift 201372
  have htrace : WordTrace (prefixWord ++ tailWord_201372) baseStart_201372 baseEnd_201372 := by
    simpa [prefixWord, tailWord_201372, baseEnd_201372] using wordTrace_append hprefix tailTrace_201372
  have hstable : (prefixWord ++ tailWord_201372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201372).length < 2 ^ (prefixWord ++ tailWord_201372).sum := by decide
  have hdescent : baseEnd_201372 < baseStart_201372 := by decide
  rcases family_descends (prefixWord ++ tailWord_201372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201376 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 3, 2, 2]
def baseStart_201376 : Nat := 118140960795 + 201376 * 2 ^ 59
def prefixEnd_201376 : Nat := 4983230072969 + 3 ^ 40 * 201376 * 2
def baseEnd_201376 : Nat := 103402680279909349173895

theorem tailTrace_201376 : CollatzResearch.WordTrace tailWord_201376 prefixEnd_201376 103402680279909349173895 := by
  unfold tailWord_201376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3672393059228309563899991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4896524078971079418533321 3672393059228309563899991)
  ·
    refine ⟨5508589588842464345849987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3672393059228309563899991 5508589588842464345849987)
    ·
      refine ⟨8262884383263696518774981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508589588842464345849987 8262884383263696518774981)
      ·
        refine ⟨1549290821861943097270309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8262884383263696518774981 1549290821861943097270309)
        ·
          refine ⟨290492029099114330738183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1549290821861943097270309 290492029099114330738183)
          ·
            refine ⟨435738043648671496107275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290492029099114330738183 435738043648671496107275)
            ·
              refine ⟨653607065473007244160913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435738043648671496107275 653607065473007244160913)
              ·
                refine ⟨490205299104755433120685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653607065473007244160913 490205299104755433120685)
                ·
                  refine ⟨183826987164283287420257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490205299104755433120685 183826987164283287420257)
                  ·
                    refine ⟨137870240373212465565193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183826987164283287420257 137870240373212465565193)
                    ·
                      refine ⟨103402680279909349173895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137870240373212465565193 103402680279909349173895)
                      ·
                        rfl

theorem cell23_201376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_201376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201376 prefixEnd_201376 := by exact prefixLift 201376
  have htrace : WordTrace (prefixWord ++ tailWord_201376) baseStart_201376 baseEnd_201376 := by
    simpa [prefixWord, tailWord_201376, baseEnd_201376] using wordTrace_append hprefix tailTrace_201376
  have hstable : (prefixWord ++ tailWord_201376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201376).length < 2 ^ (prefixWord ++ tailWord_201376).sum := by decide
  have hdescent : baseEnd_201376 < baseStart_201376 := by decide
  rcases family_descends (prefixWord ++ tailWord_201376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201392 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 4, 1, 3]
def baseStart_201392 : Nat := 118140960795 + 201392 * 2 ^ 59
def prefixEnd_201392 : Nat := 4983230072969 + 3 ^ 40 * 201392 * 2
def baseEnd_201392 : Nat := 103410895970381286573821

theorem tailTrace_201392 : CollatzResearch.WordTrace tailWord_201392 prefixEnd_201392 103410895970381286573821 := by
  unfold tailWord_201392
  simp only [CollatzResearch.WordTrace]
  refine ⟨3672684843199326930191215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4896913124265769240254953 3672684843199326930191215)
  ·
    refine ⟨5509027264798990395286823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3672684843199326930191215 5509027264798990395286823)
    ·
      refine ⟨8263540897198485592930235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509027264798990395286823 8263540897198485592930235)
      ·
        refine ⟨12395311345797728389395353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263540897198485592930235 12395311345797728389395353)
        ·
          refine ⟨9296483509348296292046515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12395311345797728389395353 9296483509348296292046515)
          ·
            refine ⟨13944725264022444438069773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9296483509348296292046515 13944725264022444438069773)
            ·
              refine ⟨5229271974008416664276165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13944725264022444438069773 5229271974008416664276165)
              ·
                refine ⟨980488495126578124551781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5229271974008416664276165 980488495126578124551781)
                ·
                  refine ⟨183841592836233398353459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980488495126578124551781 183841592836233398353459)
                  ·
                    refine ⟨275762389254350097530189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 183841592836233398353459 275762389254350097530189)
                    ·
                      refine ⟨103410895970381286573821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 275762389254350097530189 103410895970381286573821)
                      ·
                        rfl

theorem cell23_201392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 1, 3].length) (baseStart_201392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201392 prefixEnd_201392 := by exact prefixLift 201392
  have htrace : WordTrace (prefixWord ++ tailWord_201392) baseStart_201392 baseEnd_201392 := by
    simpa [prefixWord, tailWord_201392, baseEnd_201392] using wordTrace_append hprefix tailTrace_201392
  have hstable : (prefixWord ++ tailWord_201392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201392).length < 2 ^ (prefixWord ++ tailWord_201392).sum := by decide
  have hdescent : baseEnd_201392 < baseStart_201392 := by decide
  rcases family_descends (prefixWord ++ tailWord_201392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201393 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 1, 1, 4]
def baseStart_201393 : Nat := 118140960795 + 201393 * 2 ^ 59
def prefixEnd_201393 : Nat := 4983230072969 + 3 ^ 40 * 201393 * 2
def baseEnd_201393 : Nat := 103411409451035782661317

theorem tailTrace_201393 : CollatzResearch.WordTrace tailWord_201393 prefixEnd_201393 103411409451035782661317 := by
  unfold tailWord_201393
  simp only [CollatzResearch.WordTrace]
  refine ⟨7345406159395031031168833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4896937439596687354112555 7345406159395031031168833)
  ·
    refine ⟨5509054619546273273376625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7345406159395031031168833 5509054619546273273376625)
    ·
      refine ⟨4131790964659704955032469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5509054619546273273376625 4131790964659704955032469)
      ·
        refine ⟨193677701468423669767147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4131790964659704955032469 193677701468423669767147)
        ·
          refine ⟨290516552202635504650721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193677701468423669767147 290516552202635504650721)
          ·
            refine ⟨217887414151976628488041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290516552202635504650721 217887414151976628488041)
            ·
              refine ⟨163415560613982471366031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217887414151976628488041 163415560613982471366031)
              ·
                refine ⟨245123340920973707049047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163415560613982471366031 245123340920973707049047)
                ·
                  refine ⟨367685011381460560573571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245123340920973707049047 367685011381460560573571)
                  ·
                    refine ⟨551527517072190840860357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 367685011381460560573571 551527517072190840860357)
                    ·
                      refine ⟨103411409451035782661317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 551527517072190840860357 103411409451035782661317)
                      ·
                        rfl

theorem cell23_201393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_201393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201393 prefixEnd_201393 := by exact prefixLift 201393
  have htrace : WordTrace (prefixWord ++ tailWord_201393) baseStart_201393 baseEnd_201393 := by
    simpa [prefixWord, tailWord_201393, baseEnd_201393] using wordTrace_append hprefix tailTrace_201393
  have hstable : (prefixWord ++ tailWord_201393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201393).length < 2 ^ (prefixWord ++ tailWord_201393).sum := by decide
  have hdescent : baseEnd_201393 < baseStart_201393 := by decide
  rcases family_descends (prefixWord ++ tailWord_201393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201415 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_201415 : Nat := 118140960795 + 201415 * 2 ^ 59
def prefixEnd_201415 : Nat := 4983230072969 + 3 ^ 40 * 201415 * 2
def baseEnd_201415 : Nat := 103422706025434696586215

theorem tailTrace_201415 : CollatzResearch.WordTrace tailWord_201415 prefixEnd_201415 103422706025434696586215 := by
  unfold tailWord_201415
  simp only [CollatzResearch.WordTrace]
  refine ⟨7346208565315328788469699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4897472376876885858979799 7346208565315328788469699)
  ·
    refine ⟨11019312847972993182704549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7346208565315328788469699 11019312847972993182704549)
    ·
      refine ⟨2066121158994936221757103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11019312847972993182704549 2066121158994936221757103)
      ·
        refine ⟨3099181738492404332635655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066121158994936221757103 3099181738492404332635655)
        ·
          refine ⟨4648772607738606498953483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099181738492404332635655 4648772607738606498953483)
          ·
            refine ⟨6973158911607909748430225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648772607738606498953483 6973158911607909748430225)
            ·
              refine ⟨5229869183705932311322669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6973158911607909748430225 5229869183705932311322669)
              ·
                refine ⟨1961200943889724616746001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5229869183705932311322669 1961200943889724616746001)
                ·
                  refine ⟨1470900707917293462559501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1961200943889724616746001 1470900707917293462559501)
                  ·
                    refine ⟨551587765468985048459813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470900707917293462559501 551587765468985048459813)
                    ·
                      refine ⟨103422706025434696586215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 551587765468985048459813 103422706025434696586215)
                      ·
                        rfl

theorem cell23_201415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_201415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201415 prefixEnd_201415 := by exact prefixLift 201415
  have htrace : WordTrace (prefixWord ++ tailWord_201415) baseStart_201415 baseEnd_201415 := by
    simpa [prefixWord, tailWord_201415, baseEnd_201415] using wordTrace_append hprefix tailTrace_201415
  have hstable : (prefixWord ++ tailWord_201415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201415).length < 2 ^ (prefixWord ++ tailWord_201415).sum := by decide
  have hdescent : baseEnd_201415 < baseStart_201415 := by decide
  rcases family_descends (prefixWord ++ tailWord_201415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201425 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 2, 6]
def baseStart_201425 : Nat := 118140960795 + 201425 * 2 ^ 59
def prefixEnd_201425 : Nat := 4983230072969 + 3 ^ 40 * 201425 * 2
def baseEnd_201425 : Nat := 34475946943993219153723

theorem tailTrace_201425 : CollatzResearch.WordTrace tailWord_201425 prefixEnd_201425 34475946943993219153723 := by
  unfold tailWord_201425
  simp only [CollatzResearch.WordTrace]
  refine ⟨7346573295279100496333729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4897715530186066997555819 7346573295279100496333729)
  ·
    refine ⟨5509929971459325372250297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7346573295279100496333729 5509929971459325372250297)
    ·
      refine ⟨4132447478594494029187723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5509929971459325372250297 4132447478594494029187723)
      ·
        refine ⟨6198671217891741043781585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132447478594494029187723 6198671217891741043781585)
        ·
          refine ⟨4649003413418805782836189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6198671217891741043781585 4649003413418805782836189)
          ·
            refine ⟨1743376280032052168563571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4649003413418805782836189 1743376280032052168563571)
            ·
              refine ⟨2615064420048078252845357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743376280032052168563571 2615064420048078252845357)
              ·
                refine ⟨980649157518029344817009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2615064420048078252845357 980649157518029344817009)
                ·
                  refine ⟨735486868138522008612757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 980649157518029344817009 735486868138522008612757)
                  ·
                    refine ⟨34475946943993219153723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 735486868138522008612757 34475946943993219153723)
                    ·
                      rfl

theorem cell23_201425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_201425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201425 prefixEnd_201425 := by exact prefixLift 201425
  have htrace : WordTrace (prefixWord ++ tailWord_201425) baseStart_201425 baseEnd_201425 := by
    simpa [prefixWord, tailWord_201425, baseEnd_201425] using wordTrace_append hprefix tailTrace_201425
  have hstable : (prefixWord ++ tailWord_201425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201425).length < 2 ^ (prefixWord ++ tailWord_201425).sum := by decide
  have hdescent : baseEnd_201425 < baseStart_201425 := by decide
  rcases family_descends (prefixWord ++ tailWord_201425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201426 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_201426 : Nat := 118140960795 + 201426 * 2 ^ 59
def prefixEnd_201426 : Nat := 4983230072969 + 3 ^ 40 * 201426 * 2
def baseEnd_201426 : Nat := 103428354312634153548665

theorem tailTrace_201426 : CollatzResearch.WordTrace tailWord_201426 prefixEnd_201426 103428354312634153548665 := by
  unfold tailWord_201426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1836652442068869416780033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4897739845516985111413421 1836652442068869416780033)
  ·
    refine ⟨1377489331551652062585025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1836652442068869416780033 1377489331551652062585025)
    ·
      refine ⟨1033116998663739046938769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1377489331551652062585025 1033116998663739046938769)
      ·
        refine ⟨774837748997804285204077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1033116998663739046938769 774837748997804285204077)
        ·
          refine ⟨290564155874176606951529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 774837748997804285204077 290564155874176606951529)
          ·
            refine ⟨217923116905632455213647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290564155874176606951529 217923116905632455213647)
            ·
              refine ⟨326884675358448682820471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217923116905632455213647 326884675358448682820471)
              ·
                refine ⟨490327013037673024230707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326884675358448682820471 490327013037673024230707)
                ·
                  refine ⟨735490519556509536346061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490327013037673024230707 735490519556509536346061)
                  ·
                    refine ⟨275808944833691076129773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735490519556509536346061 275808944833691076129773)
                    ·
                      refine ⟨103428354312634153548665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 275808944833691076129773 103428354312634153548665)
                      ·
                        rfl

theorem cell23_201426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_201426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201426 prefixEnd_201426 := by exact prefixLift 201426
  have htrace : WordTrace (prefixWord ++ tailWord_201426) baseStart_201426 baseEnd_201426 := by
    simpa [prefixWord, tailWord_201426, baseEnd_201426] using wordTrace_append hprefix tailTrace_201426
  have hstable : (prefixWord ++ tailWord_201426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201426).length < 2 ^ (prefixWord ++ tailWord_201426).sum := by decide
  have hdescent : baseEnd_201426 < baseStart_201426 := by decide
  rcases family_descends (prefixWord ++ tailWord_201426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201449 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 4, 2, 2]
def baseStart_201449 : Nat := 118140960795 + 201449 * 2 ^ 59
def prefixEnd_201449 : Nat := 4983230072969 + 3 ^ 40 * 201449 * 2
def baseEnd_201449 : Nat := 103440164367687563561059

theorem tailTrace_201449 : CollatzResearch.WordTrace tailWord_201449 prefixEnd_201449 103440164367687563561059 := by
  unfold tailWord_201449
  simp only [CollatzResearch.WordTrace]
  refine ⟨7347448647192152595207401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4898299098128101730138267 7347448647192152595207401)
  ·
    refine ⟨5510586485394114446405551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7347448647192152595207401 5510586485394114446405551)
    ·
      refine ⟨8265879728091171669608327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5510586485394114446405551 8265879728091171669608327)
      ·
        refine ⟨12398819592136757504412491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8265879728091171669608327 12398819592136757504412491)
        ·
          refine ⟨18598229388205136256618737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12398819592136757504412491 18598229388205136256618737)
          ·
            refine ⟨13948672041153852192464053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18598229388205136256618737 13948672041153852192464053)
            ·
              refine ⟨1307688003858173643043505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13948672041153852192464053 1307688003858173643043505)
              ·
                refine ⟨980766002893630232282629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307688003858173643043505 980766002893630232282629)
                ·
                  refine ⟨183893625542555668552993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980766002893630232282629 183893625542555668552993)
                  ·
                    refine ⟨137920219156916751414745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183893625542555668552993 137920219156916751414745)
                    ·
                      refine ⟨103440164367687563561059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137920219156916751414745 103440164367687563561059)
                      ·
                        rfl

theorem cell23_201449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 2, 2].length) (baseStart_201449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201449 prefixEnd_201449 := by exact prefixLift 201449
  have htrace : WordTrace (prefixWord ++ tailWord_201449) baseStart_201449 baseEnd_201449 := by
    simpa [prefixWord, tailWord_201449, baseEnd_201449] using wordTrace_append hprefix tailTrace_201449
  have hstable : (prefixWord ++ tailWord_201449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201449).length < 2 ^ (prefixWord ++ tailWord_201449).sum := by decide
  have hdescent : baseEnd_201449 < baseStart_201449 := by decide
  rcases family_descends (prefixWord ++ tailWord_201449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201482 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_201482 : Nat := 118140960795 + 201482 * 2 ^ 59
def prefixEnd_201482 : Nat := 4983230072969 + 3 ^ 40 * 201482 * 2
def baseEnd_201482 : Nat := 103457109229285934448407

theorem tailTrace_201482 : CollatzResearch.WordTrace tailWord_201482 prefixEnd_201482 103457109229285934448407 := by
  unfold tailWord_201482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1837163064018149807789675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4899101504048399487439133 1837163064018149807789675)
  ·
    refine ⟨2755744596027224711684513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1837163064018149807789675 2755744596027224711684513)
    ·
      refine ⟨2066808447020418533763385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2755744596027224711684513 2066808447020418533763385)
      ·
        refine ⟨1550106335265313900322539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2066808447020418533763385 1550106335265313900322539)
        ·
          refine ⟨2325159502897970850483809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550106335265313900322539 2325159502897970850483809)
          ·
            refine ⟨1743869627173478137862857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325159502897970850483809 1743869627173478137862857)
            ·
              refine ⟨1307902220380108603397143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743869627173478137862857 1307902220380108603397143)
              ·
                refine ⟨1961853330570162905095715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307902220380108603397143 1961853330570162905095715)
                ·
                  refine ⟨2942779995855244357643573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961853330570162905095715 2942779995855244357643573)
                  ·
                    refine ⟨275885624611429158529085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2942779995855244357643573 275885624611429158529085)
                    ·
                      refine ⟨103457109229285934448407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 275885624611429158529085 103457109229285934448407)
                      ·
                        rfl

theorem cell23_201482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_201482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201482 prefixEnd_201482 := by exact prefixLift 201482
  have htrace : WordTrace (prefixWord ++ tailWord_201482) baseStart_201482 baseEnd_201482 := by
    simpa [prefixWord, tailWord_201482, baseEnd_201482] using wordTrace_append hprefix tailTrace_201482
  have hstable : (prefixWord ++ tailWord_201482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201482).length < 2 ^ (prefixWord ++ tailWord_201482).sum := by decide
  have hdescent : baseEnd_201482 < baseStart_201482 := by decide
  rcases family_descends (prefixWord ++ tailWord_201482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201512 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_201512 : Nat := 118140960795 + 201512 * 2 ^ 59
def prefixEnd_201512 : Nat := 4983230072969 + 3 ^ 40 * 201512 * 2
def baseEnd_201512 : Nat := 103472513648920817073269

theorem tailTrace_201512 : CollatzResearch.WordTrace tailWord_201512 prefixEnd_201512 103472513648920817073269 := by
  unfold tailWord_201512
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674873222981957177375395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4899830963975942903167193 3674873222981957177375395)
  ·
    refine ⟨5512309834472935766063093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674873222981957177375395 5512309834472935766063093)
    ·
      refine ⟨516779046981837728068415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5512309834472935766063093 516779046981837728068415)
      ·
        refine ⟨775168570472756592102623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516779046981837728068415 775168570472756592102623)
        ·
          refine ⟨1162752855709134888153935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775168570472756592102623 1162752855709134888153935)
          ·
            refine ⟨1744129283563702332230903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162752855709134888153935 1744129283563702332230903)
            ·
              refine ⟨2616193925345553498346355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744129283563702332230903 2616193925345553498346355)
              ·
                refine ⟨3924290888018330247519533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616193925345553498346355 3924290888018330247519533)
                ·
                  refine ⟨1471609083006873842819825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3924290888018330247519533 1471609083006873842819825)
                  ·
                    refine ⟨1103706812255155382114869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1471609083006873842819825 1103706812255155382114869)
                    ·
                      refine ⟨103472513648920817073269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1103706812255155382114869 103472513648920817073269)
                      ·
                        rfl

theorem cell23_201512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_201512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201512 prefixEnd_201512 := by exact prefixLift 201512
  have htrace : WordTrace (prefixWord ++ tailWord_201512) baseStart_201512 baseEnd_201512 := by
    simpa [prefixWord, tailWord_201512, baseEnd_201512] using wordTrace_append hprefix tailTrace_201512
  have hstable : (prefixWord ++ tailWord_201512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201512).length < 2 ^ (prefixWord ++ tailWord_201512).sum := by decide
  have hdescent : baseEnd_201512 < baseStart_201512 := by decide
  rcases family_descends (prefixWord ++ tailWord_201512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201517 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_201517 : Nat := 118140960795 + 201517 * 2 ^ 59
def prefixEnd_201517 : Nat := 4983230072969 + 3 ^ 40 * 201517 * 2
def baseEnd_201517 : Nat := 103475081052193297510747

theorem tailTrace_201517 : CollatzResearch.WordTrace tailWord_201517 prefixEnd_201517 103475081052193297510747 := by
  unfold tailWord_201517
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349928810945800208682805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4899952540630533472455203 7349928810945800208682805)
  ·
    refine ⟨689055826026168769564013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7349928810945800208682805 689055826026168769564013)
    ·
      refine ⟨258395934759813288586505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 689055826026168769564013 258395934759813288586505)
      ·
        refine ⟨193796951069859966439879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258395934759813288586505 193796951069859966439879)
        ·
          refine ⟨290695426604789949659819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193796951069859966439879 290695426604789949659819)
          ·
            refine ⟨436043139907184924489729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290695426604789949659819 436043139907184924489729)
            ·
              refine ⟨327032354930388693367297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436043139907184924489729 327032354930388693367297)
              ·
                refine ⟨245274266197791520025473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327032354930388693367297 245274266197791520025473)
                ·
                  refine ⟨183955699648343640019105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245274266197791520025473 183955699648343640019105)
                  ·
                    refine ⟨137966774736257730014329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183955699648343640019105 137966774736257730014329)
                    ·
                      refine ⟨103475081052193297510747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137966774736257730014329 103475081052193297510747)
                      ·
                        rfl

theorem cell23_201517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_201517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201517 prefixEnd_201517 := by exact prefixLift 201517
  have htrace : WordTrace (prefixWord ++ tailWord_201517) baseStart_201517 baseEnd_201517 := by
    simpa [prefixWord, tailWord_201517, baseEnd_201517] using wordTrace_append hprefix tailTrace_201517
  have hstable : (prefixWord ++ tailWord_201517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201517).length < 2 ^ (prefixWord ++ tailWord_201517).sum := by decide
  have hdescent : baseEnd_201517 < baseStart_201517 := by decide
  rcases family_descends (prefixWord ++ tailWord_201517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201539 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 2, 4, 2]
def baseStart_201539 : Nat := 118140960795 + 201539 * 2 ^ 59
def prefixEnd_201539 : Nat := 4983230072969 + 3 ^ 40 * 201539 * 2
def baseEnd_201539 : Nat := 103486377626592211435645

theorem tailTrace_201539 : CollatzResearch.WordTrace tailWord_201539 prefixEnd_201539 103486377626592211435645 := by
  unfold tailWord_201539
  simp only [CollatzResearch.WordTrace]
  refine ⟨7350731216866097965983671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4900487477910731977322447 7350731216866097965983671)
  ·
    refine ⟨11026096825299146948975507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7350731216866097965983671 11026096825299146948975507)
    ·
      refine ⟨16539145237948720423463261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11026096825299146948975507 16539145237948720423463261)
      ·
        refine ⟨6202179464230770158798723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16539145237948720423463261 6202179464230770158798723)
        ·
          refine ⟨9303269196346155238198085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202179464230770158798723 9303269196346155238198085)
          ·
            refine ⟨1744362974314904107162141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9303269196346155238198085 1744362974314904107162141)
            ·
              refine ⟨654136115368089040185803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1744362974314904107162141 654136115368089040185803)
              ·
                refine ⟨981204173052133560278705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654136115368089040185803 981204173052133560278705)
                ·
                  refine ⟨735903129789100170209029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 981204173052133560278705 735903129789100170209029)
                  ·
                    refine ⟨137981836835456281914193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 735903129789100170209029 137981836835456281914193)
                    ·
                      refine ⟨103486377626592211435645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 137981836835456281914193 103486377626592211435645)
                      ·
                        rfl

theorem cell23_201539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_201539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201539 prefixEnd_201539 := by exact prefixLift 201539
  have htrace : WordTrace (prefixWord ++ tailWord_201539) baseStart_201539 baseEnd_201539 := by
    simpa [prefixWord, tailWord_201539, baseEnd_201539] using wordTrace_append hprefix tailTrace_201539
  have hstable : (prefixWord ++ tailWord_201539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201539).length < 2 ^ (prefixWord ++ tailWord_201539).sum := by decide
  have hdescent : baseEnd_201539 < baseStart_201539 := by decide
  rcases family_descends (prefixWord ++ tailWord_201539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201559 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_201559 : Nat := 118140960795 + 201559 * 2 ^ 59
def prefixEnd_201559 : Nat := 4983230072969 + 3 ^ 40 * 201559 * 2
def baseEnd_201559 : Nat := 103496647239682133185553

theorem tailTrace_201559 : CollatzResearch.WordTrace tailWord_201559 prefixEnd_201559 103496647239682133185553 := by
  unfold tailWord_201559
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351460676793641381711731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4900973784529094254474487 7351460676793641381711731)
  ·
    refine ⟨11027191015190462072567597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7351460676793641381711731 11027191015190462072567597)
    ·
      refine ⟨4135196630696423277212849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11027191015190462072567597 4135196630696423277212849)
      ·
        refine ⟨3101397473022317457909637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4135196630696423277212849 3101397473022317457909637)
        ·
          refine ⟨581512026191684523358057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3101397473022317457909637 581512026191684523358057)
          ·
            refine ⟨436134019643763392518543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581512026191684523358057 436134019643763392518543)
            ·
              refine ⟨654201029465645088777815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436134019643763392518543 654201029465645088777815)
              ·
                refine ⟨981301544198467633166723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654201029465645088777815 981301544198467633166723)
                ·
                  refine ⟨1471952316297701449750085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981301544198467633166723 1471952316297701449750085)
                  ·
                    refine ⟨275991059305819021828141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471952316297701449750085 275991059305819021828141)
                    ·
                      refine ⟨103496647239682133185553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 275991059305819021828141 103496647239682133185553)
                      ·
                        rfl

theorem cell23_201559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_201559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201559 prefixEnd_201559 := by exact prefixLift 201559
  have htrace : WordTrace (prefixWord ++ tailWord_201559) baseStart_201559 baseEnd_201559 := by
    simpa [prefixWord, tailWord_201559, baseEnd_201559] using wordTrace_append hprefix tailTrace_201559
  have hstable : (prefixWord ++ tailWord_201559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201559).length < 2 ^ (prefixWord ++ tailWord_201559).sum := by decide
  have hdescent : baseEnd_201559 < baseStart_201559 := by decide
  rcases family_descends (prefixWord ++ tailWord_201559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201592 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 3, 5]
def baseStart_201592 : Nat := 118140960795 + 201592 * 2 ^ 59
def prefixEnd_201592 : Nat := 4983230072969 + 3 ^ 40 * 201592 * 2
def baseEnd_201592 : Nat := 34504530700426834690967

theorem tailTrace_201592 : CollatzResearch.WordTrace tailWord_201592 prefixEnd_201592 34504530700426834690967 := by
  unfold tailWord_201592
  simp only [CollatzResearch.WordTrace]
  refine ⟨3676332142837044008831515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4901776190449392011775353 3676332142837044008831515)
  ·
    refine ⟨5514498214255566013247273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3676332142837044008831515 5514498214255566013247273)
    ·
      refine ⟨4135873660691674509935455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5514498214255566013247273 4135873660691674509935455)
      ·
        refine ⟨6203810491037511764903183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135873660691674509935455 6203810491037511764903183)
        ·
          refine ⟨9305715736556267647354775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203810491037511764903183 9305715736556267647354775)
          ·
            refine ⟨13958573604834401471032163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305715736556267647354775 13958573604834401471032163)
            ·
              refine ⟨20937860407251602206548245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13958573604834401471032163 20937860407251602206548245)
              ·
                refine ⟨981462206589918853431949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20937860407251602206548245 981462206589918853431949)
                ·
                  refine ⟨368048327471219570036981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981462206589918853431949 368048327471219570036981)
                  ·
                    refine ⟨34504530700426834690967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 368048327471219570036981 34504530700426834690967)
                    ·
                      rfl

theorem cell23_201592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_201592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201592 prefixEnd_201592 := by exact prefixLift 201592
  have htrace : WordTrace (prefixWord ++ tailWord_201592) baseStart_201592 baseEnd_201592 := by
    simpa [prefixWord, tailWord_201592, baseEnd_201592] using wordTrace_append hprefix tailTrace_201592
  have hstable : (prefixWord ++ tailWord_201592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201592).length < 2 ^ (prefixWord ++ tailWord_201592).sum := by decide
  have hdescent : baseEnd_201592 < baseStart_201592 := by decide
  rcases family_descends (prefixWord ++ tailWord_201592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201599 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 1, 5, 2]
def baseStart_201599 : Nat := 118140960795 + 201599 * 2 ^ 59
def prefixEnd_201599 : Nat := 4983230072969 + 3 ^ 40 * 201599 * 2
def baseEnd_201599 : Nat := 103517186465861976685369

theorem tailTrace_201599 : CollatzResearch.WordTrace tailWord_201599 prefixEnd_201599 103517186465861976685369 := by
  unfold tailWord_201599
  simp only [CollatzResearch.WordTrace]
  refine ⟨7352919596648728213167851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4901946397765818808778567 7352919596648728213167851)
  ·
    refine ⟨11029379394973092319751777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7352919596648728213167851 11029379394973092319751777)
    ·
      refine ⟨8272034546229819239813833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11029379394973092319751777 8272034546229819239813833)
      ·
        refine ⟨6204025909672364429860375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8272034546229819239813833 6204025909672364429860375)
        ·
          refine ⟨9306038864508546644790563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6204025909672364429860375 9306038864508546644790563)
          ·
            refine ⟨13959058296762819967185845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9306038864508546644790563 13959058296762819967185845)
            ·
              refine ⟨1308661715321514371923673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13959058296762819967185845 1308661715321514371923673)
              ·
                refine ⟨981496286491135778942755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308661715321514371923673 981496286491135778942755)
                ·
                  refine ⟨1472244429736703668414133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981496286491135778942755 1472244429736703668414133)
                  ·
                    refine ⟨138022915287815968913825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1472244429736703668414133 138022915287815968913825)
                    ·
                      refine ⟨103517186465861976685369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 138022915287815968913825 103517186465861976685369)
                      ·
                        rfl

theorem cell23_201599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_201599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201599 prefixEnd_201599 := by exact prefixLift 201599
  have htrace : WordTrace (prefixWord ++ tailWord_201599) baseStart_201599 baseEnd_201599 := by
    simpa [prefixWord, tailWord_201599, baseEnd_201599] using wordTrace_append hprefix tailTrace_201599
  have hstable : (prefixWord ++ tailWord_201599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201599).length < 2 ^ (prefixWord ++ tailWord_201599).sum := by decide
  have hdescent : baseEnd_201599 < baseStart_201599 := by decide
  rcases family_descends (prefixWord ++ tailWord_201599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201609 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 1, 5]
def baseStart_201609 : Nat := 118140960795 + 201609 * 2 ^ 59
def prefixEnd_201609 : Nat := 4983230072969 + 3 ^ 40 * 201609 * 2
def baseEnd_201609 : Nat := 34507440424135645853441

theorem tailTrace_201609 : CollatzResearch.WordTrace tailWord_201609 prefixEnd_201609 34507440424135645853441 := by
  unfold tailWord_201609
  simp only [CollatzResearch.WordTrace]
  refine ⟨7353284326612499921031881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4902189551074999947354587 7353284326612499921031881)
  ·
    refine ⟨5514963244959374940773911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7353284326612499921031881 5514963244959374940773911)
    ·
      refine ⟨8272444867439062411160867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5514963244959374940773911 8272444867439062411160867)
      ·
        refine ⟨12408667301158593616741301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272444867439062411160867 12408667301158593616741301)
        ·
          refine ⟨1163312559483618151569497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12408667301158593616741301 1163312559483618151569497)
          ·
            refine ⟨872484419612713613677123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163312559483618151569497 872484419612713613677123)
            ·
              refine ⟨1308726629419070420515685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872484419612713613677123 1308726629419070420515685)
              ·
                refine ⟨245386243016075703846691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1308726629419070420515685 245386243016075703846691)
                ·
                  refine ⟨368079364524113555770037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245386243016075703846691 368079364524113555770037)
                  ·
                    refine ⟨34507440424135645853441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 368079364524113555770037 34507440424135645853441)
                    ·
                      rfl

theorem cell23_201609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 5].length) (baseStart_201609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_201609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_201609 prefixEnd_201609 := by exact prefixLift 201609
  have htrace : WordTrace (prefixWord ++ tailWord_201609) baseStart_201609 baseEnd_201609 := by
    simpa [prefixWord, tailWord_201609, baseEnd_201609] using wordTrace_append hprefix tailTrace_201609
  have hstable : (prefixWord ++ tailWord_201609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201609).length < 2 ^ (prefixWord ++ tailWord_201609).sum := by decide
  have hdescent : baseEnd_201609 < baseStart_201609 := by decide
  rcases family_descends (prefixWord ++ tailWord_201609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
