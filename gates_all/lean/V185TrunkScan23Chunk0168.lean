import V185TrunkScan23Chunk0167

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_993350 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_993350 : Nat := 118140960795 + 993350 * 2 ^ 59
def prefixEnd_993350 : Nat := 4983230072969 + 3 ^ 40 * 993350 * 2
def baseEnd_993350 : Nat := 510066008143793747256673

theorem tailTrace_993350 : CollatzResearch.WordTrace tailWord_993350 prefixEnd_993350 510066008143793747256673 := by
  unfold tailWord_993350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132201592227189859954047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24153633967513383679019669 1132201592227189859954047)
  ·
    refine ⟨1698302388340784789931071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1132201592227189859954047 1698302388340784789931071)
    ·
      refine ⟨2547453582511177184896607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698302388340784789931071 2547453582511177184896607)
      ·
        refine ⟨3821180373766765777344911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547453582511177184896607 3821180373766765777344911)
        ·
          refine ⟨5731770560650148666017367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3821180373766765777344911 5731770560650148666017367)
          ·
            refine ⟨8597655840975222999026051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5731770560650148666017367 8597655840975222999026051)
            ·
              refine ⟨12896483761462834498539077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8597655840975222999026051 12896483761462834498539077)
              ·
                refine ⟨2418090705274281468476077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12896483761462834498539077 2418090705274281468476077)
                ·
                  refine ⟨906784014477855550678529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2418090705274281468476077 906784014477855550678529)
                  ·
                    refine ⟨680088010858391663008897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 906784014477855550678529 680088010858391663008897)
                    ·
                      refine ⟨510066008143793747256673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 680088010858391663008897 510066008143793747256673)
                      ·
                        rfl

theorem cell23_993350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_993350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993350 prefixEnd_993350 := by exact prefixLift 993350
  have htrace : WordTrace (prefixWord ++ tailWord_993350) baseStart_993350 baseEnd_993350 := by
    simpa [prefixWord, tailWord_993350, baseEnd_993350] using wordTrace_append hprefix tailTrace_993350
  have hstable : (prefixWord ++ tailWord_993350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993350).length < 2 ^ (prefixWord ++ tailWord_993350).sum := by decide
  have hdescent : baseEnd_993350 < baseStart_993350 := by decide
  rcases family_descends (prefixWord ++ tailWord_993350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993389 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_993389 : Nat := 118140960795 + 993389 * 2 ^ 59
def prefixEnd_993389 : Nat := 4983230072969 + 3 ^ 40 * 993389 * 2
def baseEnd_993389 : Nat := 510086033889319094668993

theorem tailTrace_993389 : CollatzResearch.WordTrace tailWord_993389 prefixEnd_993389 510086033889319094668993 := by
  unfold tailWord_993389
  simp only [CollatzResearch.WordTrace]
  refine ⟨36231873398128785179199221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24154582265419190119466147 36231873398128785179199221)
  ·
    refine ⟨3396738131074573610549927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36231873398128785179199221 3396738131074573610549927)
    ·
      refine ⟨5095107196611860415824891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3396738131074573610549927 5095107196611860415824891)
      ·
        refine ⟨7642660794917790623737337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5095107196611860415824891 7642660794917790623737337)
        ·
          refine ⟨5731995596188342967803003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7642660794917790623737337 5731995596188342967803003)
          ·
            refine ⟨8597993394282514451704505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5731995596188342967803003 8597993394282514451704505)
            ·
              refine ⟨6448495045711885838778379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8597993394282514451704505 6448495045711885838778379)
              ·
                refine ⟨9672742568567828758167569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6448495045711885838778379 9672742568567828758167569)
                ·
                  refine ⟨7254556926425871568625677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9672742568567828758167569 7254556926425871568625677)
                  ·
                    refine ⟨2720458847409701838234629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7254556926425871568625677 2720458847409701838234629)
                    ·
                      refine ⟨510086033889319094668993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2720458847409701838234629 510086033889319094668993)
                      ·
                        rfl

theorem cell23_993389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_993389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993389 prefixEnd_993389 := by exact prefixLift 993389
  have htrace : WordTrace (prefixWord ++ tailWord_993389) baseStart_993389 baseEnd_993389 := by
    simpa [prefixWord, tailWord_993389, baseEnd_993389] using wordTrace_append hprefix tailTrace_993389
  have hstable : (prefixWord ++ tailWord_993389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993389).length < 2 ^ (prefixWord ++ tailWord_993389).sum := by decide
  have hdescent : baseEnd_993389 < baseStart_993389 := by decide
  rcases family_descends (prefixWord ++ tailWord_993389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993402 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_993402 : Nat := 118140960795 + 993402 * 2 ^ 59
def prefixEnd_993402 : Nat := 4983230072969 + 3 ^ 40 * 993402 * 2
def baseEnd_993402 : Nat := 510092709137827543806433

theorem tailTrace_993402 : CollatzResearch.WordTrace tailWord_993402 prefixEnd_993402 510092709137827543806433 := by
  unfold tailWord_993402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058086886770422099855615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24154898364721125599614973 9058086886770422099855615)
  ·
    refine ⟨13587130330155633149783423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9058086886770422099855615 13587130330155633149783423)
    ·
      refine ⟨20380695495233449724675135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13587130330155633149783423 20380695495233449724675135)
      ·
        refine ⟨30571043242850174587012703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20380695495233449724675135 30571043242850174587012703)
        ·
          refine ⟨45856564864275261880519055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30571043242850174587012703 45856564864275261880519055)
          ·
            refine ⟨68784847296412892820778583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45856564864275261880519055 68784847296412892820778583)
            ·
              refine ⟨103177270944619339231167875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68784847296412892820778583 103177270944619339231167875)
              ·
                refine ⟨154765906416929008846751813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103177270944619339231167875 154765906416929008846751813)
                ·
                  refine ⟨29018607453174189158765965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154765906416929008846751813 29018607453174189158765965)
                  ·
                    refine ⟨10881977794940320934537237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29018607453174189158765965 10881977794940320934537237)
                    ·
                      refine ⟨510092709137827543806433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10881977794940320934537237 510092709137827543806433)
                      ·
                        rfl

theorem cell23_993402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_993402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993402 prefixEnd_993402 := by exact prefixLift 993402
  have htrace : WordTrace (prefixWord ++ tailWord_993402) baseStart_993402 baseEnd_993402 := by
    simpa [prefixWord, tailWord_993402, baseEnd_993402] using wordTrace_append hprefix tailTrace_993402
  have hstable : (prefixWord ++ tailWord_993402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993402).length < 2 ^ (prefixWord ++ tailWord_993402).sum := by decide
  have hdescent : baseEnd_993402 < baseStart_993402 := by decide
  rcases family_descends (prefixWord ++ tailWord_993402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993440 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 2, 2, 2]
def baseStart_993440 : Nat := 118140960795 + 993440 * 2 ^ 59
def prefixEnd_993440 : Nat := 4983230072969 + 3 ^ 40 * 993440 * 2
def baseEnd_993440 : Nat := 510112221402698395131259

theorem tailTrace_993440 : CollatzResearch.WordTrace tailWord_993440 prefixEnd_993440 510112221402698395131259 := by
  unfold tailWord_993440
  simp only [CollatzResearch.WordTrace]
  refine ⟨18116866760472010444652887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24155822347296013926203849 18116866760472010444652887)
  ·
    refine ⟨27175300140708015666979331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18116866760472010444652887 27175300140708015666979331)
    ·
      refine ⟨40762950211062023500468997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27175300140708015666979331 40762950211062023500468997)
      ·
        refine ⟨7643053164574129406337937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40762950211062023500468997 7643053164574129406337937)
        ·
          refine ⟨5732289873430597054753453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7643053164574129406337937 5732289873430597054753453)
          ·
            refine ⟨2149608702536473895532545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5732289873430597054753453 2149608702536473895532545)
            ·
              refine ⟨1612206526902355421649409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2149608702536473895532545 1612206526902355421649409)
              ·
                refine ⟨1209154895176766566237057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612206526902355421649409 1209154895176766566237057)
                ·
                  refine ⟨906866171382574924677793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1209154895176766566237057 906866171382574924677793)
                  ·
                    refine ⟨680149628536931193508345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 906866171382574924677793 680149628536931193508345)
                    ·
                      refine ⟨510112221402698395131259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 680149628536931193508345 510112221402698395131259)
                      ·
                        rfl

theorem cell23_993440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_993440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993440 prefixEnd_993440 := by exact prefixLift 993440
  have htrace : WordTrace (prefixWord ++ tailWord_993440) baseStart_993440 baseEnd_993440 := by
    simpa [prefixWord, tailWord_993440, baseEnd_993440] using wordTrace_append hprefix tailTrace_993440
  have hstable : (prefixWord ++ tailWord_993440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993440).length < 2 ^ (prefixWord ++ tailWord_993440).sum := by decide
  have hdescent : baseEnd_993440 < baseStart_993440 := by decide
  rcases family_descends (prefixWord ++ tailWord_993440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993476 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_993476 : Nat := 118140960795 + 993476 * 2 ^ 59
def prefixEnd_993476 : Nat := 4983230072969 + 3 ^ 40 * 993476 * 2
def baseEnd_993476 : Nat := 170043568902086751427031

theorem tailTrace_993476 : CollatzResearch.WordTrace tailWord_993476 prefixEnd_993476 170043568902086751427031 := by
  unfold tailWord_993476
  simp only [CollatzResearch.WordTrace]
  refine ⟨18117523274406799518808141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24156697699209066025077521 18117523274406799518808141)
  ·
    refine ⟨6794071227902549819553053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18117523274406799518808141 6794071227902549819553053)
    ·
      refine ⟨2547776710463456182332395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6794071227902549819553053 2547776710463456182332395)
      ·
        refine ⟨3821665065695184273498593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547776710463456182332395 3821665065695184273498593)
        ·
          refine ⟨2866248799271388205123945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3821665065695184273498593 2866248799271388205123945)
          ·
            refine ⟨2149686599453541153842959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866248799271388205123945 2149686599453541153842959)
            ·
              refine ⟨3224529899180311730764439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149686599453541153842959 3224529899180311730764439)
              ·
                refine ⟨4836794848770467596146659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224529899180311730764439 4836794848770467596146659)
                ·
                  refine ⟨7255192273155701394219989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836794848770467596146659 7255192273155701394219989)
                  ·
                    refine ⟨170043568902086751427031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7255192273155701394219989 170043568902086751427031)
                    ·
                      rfl

theorem cell23_993476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_993476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993476 prefixEnd_993476 := by exact prefixLift 993476
  have htrace : WordTrace (prefixWord ++ tailWord_993476) baseStart_993476 baseEnd_993476 := by
    simpa [prefixWord, tailWord_993476, baseEnd_993476] using wordTrace_append hprefix tailTrace_993476
  have hstable : (prefixWord ++ tailWord_993476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993476).length < 2 ^ (prefixWord ++ tailWord_993476).sum := by decide
  have hdescent : baseEnd_993476 < baseStart_993476 := by decide
  rcases family_descends (prefixWord ++ tailWord_993476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993499 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 3]
def baseStart_993499 : Nat := 118140960795 + 993499 * 2 ^ 59
def prefixEnd_993499 : Nat := 4983230072969 + 3 ^ 40 * 993499 * 2
def baseEnd_993499 : Nat := 510142516761313664293487

theorem tailTrace_993499 : CollatzResearch.WordTrace tailWord_993499 prefixEnd_993499 510142516761313664293487 := by
  unfold tailWord_993499
  simp only [CollatzResearch.WordTrace]
  refine ⟨36235885427730273965703551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24157256951820182643802367 36235885427730273965703551)
  ·
    refine ⟨54353828141595410948555327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36235885427730273965703551 54353828141595410948555327)
    ·
      refine ⟨81530742212393116422832991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54353828141595410948555327 81530742212393116422832991)
      ·
        refine ⟨122296113318589674634249487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81530742212393116422832991 122296113318589674634249487)
        ·
          refine ⟨183444169977884511951374231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122296113318589674634249487 183444169977884511951374231)
          ·
            refine ⟨275166254966826767927061347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183444169977884511951374231 275166254966826767927061347)
            ·
              refine ⟨412749382450240151890592021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275166254966826767927061347 412749382450240151890592021)
              ·
                refine ⟨19347627302355007119871501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 412749382450240151890592021 19347627302355007119871501)
                ·
                  refine ⟨7255360238383127669951813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19347627302355007119871501 7255360238383127669951813)
                  ·
                    refine ⟨1360380044696836438115965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7255360238383127669951813 1360380044696836438115965)
                    ·
                      refine ⟨510142516761313664293487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1360380044696836438115965 510142516761313664293487)
                      ·
                        rfl

theorem cell23_993499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 3].length) (baseStart_993499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993499 prefixEnd_993499 := by exact prefixLift 993499
  have htrace : WordTrace (prefixWord ++ tailWord_993499) baseStart_993499 baseEnd_993499 := by
    simpa [prefixWord, tailWord_993499, baseEnd_993499] using wordTrace_append hprefix tailTrace_993499
  have hstable : (prefixWord ++ tailWord_993499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993499).length < 2 ^ (prefixWord ++ tailWord_993499).sum := by decide
  have hdescent : baseEnd_993499 < baseStart_993499 := by decide
  rcases family_descends (prefixWord ++ tailWord_993499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993563 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 3]
def baseStart_993563 : Nat := 118140960795 + 993563 * 2 ^ 59
def prefixEnd_993563 : Nat := 4983230072969 + 3 ^ 40 * 993563 * 2
def baseEnd_993563 : Nat := 510175379523201413893193

theorem tailTrace_993563 : CollatzResearch.WordTrace tailWord_993563 prefixEnd_993563 510175379523201413893193 := by
  unfold tailWord_993563
  simp only [CollatzResearch.WordTrace]
  refine ⟨36238219699498412896033343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24158813132998941930688895 36238219699498412896033343)
  ·
    refine ⟨54357329549247619344050015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36238219699498412896033343 54357329549247619344050015)
    ·
      refine ⟨81535994323871429016075023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54357329549247619344050015 81535994323871429016075023)
      ·
        refine ⟨122303991485807143524112535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81535994323871429016075023 122303991485807143524112535)
        ·
          refine ⟨183455987228710715286168803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122303991485807143524112535 183455987228710715286168803)
          ·
            refine ⟨275183980843066072929253205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183455987228710715286168803 275183980843066072929253205)
            ·
              refine ⟨1612406137752340271069843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 275183980843066072929253205 1612406137752340271069843)
              ·
                refine ⟨2418609206628510406604765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612406137752340271069843 2418609206628510406604765)
                ·
                  refine ⟨906978452485691402476787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2418609206628510406604765 906978452485691402476787)
                  ·
                    refine ⟨1360467678728537103715181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 906978452485691402476787 1360467678728537103715181)
                    ·
                      refine ⟨510175379523201413893193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1360467678728537103715181 510175379523201413893193)
                      ·
                        rfl

theorem cell23_993563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 3].length) (baseStart_993563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993563 prefixEnd_993563 := by exact prefixLift 993563
  have htrace : WordTrace (prefixWord ++ tailWord_993563) baseStart_993563 baseEnd_993563 := by
    simpa [prefixWord, tailWord_993563, baseEnd_993563] using wordTrace_append hprefix tailTrace_993563
  have hstable : (prefixWord ++ tailWord_993563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993563).length < 2 ^ (prefixWord ++ tailWord_993563).sum := by decide
  have hdescent : baseEnd_993563 < baseStart_993563 := by decide
  rcases family_descends (prefixWord ++ tailWord_993563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993570 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 6]
def baseStart_993570 : Nat := 118140960795 + 993570 * 2 ^ 59
def prefixEnd_993570 : Nat := 4983230072969 + 3 ^ 40 * 993570 * 2
def baseEnd_993570 : Nat := 56686552654198098500629

theorem tailTrace_993570 : CollatzResearch.WordTrace tailWord_993570 prefixEnd_993570 56686552654198098500629 := by
  unfold tailWord_993570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9059618752618263272884541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24158983340315368727692109 9059618752618263272884541)
  ·
    refine ⟨3397357032231848727331703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9059618752618263272884541 3397357032231848727331703)
    ·
      refine ⟨5096035548347773090997555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3397357032231848727331703 5096035548347773090997555)
      ·
        refine ⟨7644053322521659636496333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096035548347773090997555 7644053322521659636496333)
        ·
          refine ⟨2866519995945622363686125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7644053322521659636496333 2866519995945622363686125)
          ·
            refine ⟨1074944998479608386382297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2866519995945622363686125 1074944998479608386382297)
            ·
              refine ⟨806208748859706289786723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074944998479608386382297 806208748859706289786723)
              ·
                refine ⟨1209313123289559434680085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806208748859706289786723 1209313123289559434680085)
                ·
                  refine ⟨56686552654198098500629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1209313123289559434680085 56686552654198098500629)
                  ·
                    rfl

theorem cell23_993570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_993570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993570 prefixEnd_993570 := by exact prefixLift 993570
  have htrace : WordTrace (prefixWord ++ tailWord_993570) baseStart_993570 baseEnd_993570 := by
    simpa [prefixWord, tailWord_993570, baseEnd_993570] using wordTrace_append hprefix tailTrace_993570
  have hstable : (prefixWord ++ tailWord_993570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993570).length < 2 ^ (prefixWord ++ tailWord_993570).sum := by decide
  have hdescent : baseEnd_993570 < baseStart_993570 := by decide
  rcases family_descends (prefixWord ++ tailWord_993570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993596 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_993596 : Nat := 118140960795 + 993596 * 2 ^ 59
def prefixEnd_993596 : Nat := 4983230072969 + 3 ^ 40 * 993596 * 2
def baseEnd_993596 : Nat := 170064108128266594926847

theorem tailTrace_993596 : CollatzResearch.WordTrace tailWord_993596 prefixEnd_993596 170064108128266594926847 := by
  unfold tailWord_993596
  simp only [CollatzResearch.WordTrace]
  refine ⟨18119711654189429765992321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24159615538919239687989761 18119711654189429765992321)
  ·
    refine ⟨13589783740642072324494241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18119711654189429765992321 13589783740642072324494241)
    ·
      refine ⟨10192337805481554243370681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13589783740642072324494241 10192337805481554243370681)
      ·
        refine ⟨7644253354111165682528011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10192337805481554243370681 7644253354111165682528011)
        ·
          refine ⟨11466380031166748523792017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7644253354111165682528011 11466380031166748523792017)
          ·
            refine ⟨8599785023375061392844013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11466380031166748523792017 8599785023375061392844013)
            ·
              refine ⟨3224919383765648022316505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8599785023375061392844013 3224919383765648022316505)
              ·
                refine ⟨2418689537824236016737379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3224919383765648022316505 2418689537824236016737379)
                ·
                  refine ⟨3628034306736354025106069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418689537824236016737379 3628034306736354025106069)
                  ·
                    refine ⟨170064108128266594926847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3628034306736354025106069 170064108128266594926847)
                    ·
                      rfl

theorem cell23_993596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_993596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993596 prefixEnd_993596 := by exact prefixLift 993596
  have htrace : WordTrace (prefixWord ++ tailWord_993596) baseStart_993596 baseEnd_993596 := by
    simpa [prefixWord, tailWord_993596, baseEnd_993596] using wordTrace_append hprefix tailTrace_993596
  have hstable : (prefixWord ++ tailWord_993596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993596).length < 2 ^ (prefixWord ++ tailWord_993596).sum := by decide
  have hdescent : baseEnd_993596 < baseStart_993596 := by decide
  rcases family_descends (prefixWord ++ tailWord_993596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993619 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 7]
def baseStart_993619 : Nat := 118140960795 + 993619 * 2 ^ 59
def prefixEnd_993619 : Nat := 4983230072969 + 3 ^ 40 * 993619 * 2
def baseEnd_993619 : Nat := 510204134439853194792935

theorem tailTrace_993619 : CollatzResearch.WordTrace tailWord_993619 prefixEnd_993619 510204134439853194792935 := by
  unfold tailWord_993619
  simp only [CollatzResearch.WordTrace]
  refine ⟨36240262187295534460071911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24160174791530356306714607 36240262187295534460071911)
  ·
    refine ⟨54360393280943301690107867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36240262187295534460071911 54360393280943301690107867)
    ·
      refine ⟨81540589921414952535161801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54360393280943301690107867 81540589921414952535161801)
      ·
        refine ⟨61155442441061214401371351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81540589921414952535161801 61155442441061214401371351)
        ·
          refine ⟨91733163661591821602057027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61155442441061214401371351 91733163661591821602057027)
          ·
            refine ⟨137599745492387732403085541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91733163661591821602057027 137599745492387732403085541)
            ·
              refine ⟨25799952279822699825578539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137599745492387732403085541 25799952279822699825578539)
              ·
                refine ⟨38699928419734049738367809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25799952279822699825578539 38699928419734049738367809)
                ·
                  refine ⟨29024946314800537303775857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38699928419734049738367809 29024946314800537303775857)
                  ·
                    refine ⟨21768709736100402977831893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29024946314800537303775857 21768709736100402977831893)
                    ·
                      refine ⟨510204134439853194792935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21768709736100402977831893 510204134439853194792935)
                      ·
                        rfl

theorem cell23_993619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_993619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993619 prefixEnd_993619 := by exact prefixLift 993619
  have htrace : WordTrace (prefixWord ++ tailWord_993619) baseStart_993619 baseEnd_993619 := by
    simpa [prefixWord, tailWord_993619, baseEnd_993619] using wordTrace_append hprefix tailTrace_993619
  have hstable : (prefixWord ++ tailWord_993619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993619).length < 2 ^ (prefixWord ++ tailWord_993619).sum := by decide
  have hdescent : baseEnd_993619 < baseStart_993619 := by decide
  rcases family_descends (prefixWord ++ tailWord_993619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993713 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_993713 : Nat := 118140960795 + 993713 * 2 ^ 59
def prefixEnd_993713 : Nat := 4983230072969 + 3 ^ 40 * 993713 * 2
def baseEnd_993713 : Nat := 510252401621375827017503

theorem tailTrace_993713 : CollatzResearch.WordTrace tailWord_993713 prefixEnd_993713 510252401621375827017503 := by
  unfold tailWord_993713
  simp only [CollatzResearch.WordTrace]
  refine ⟨36243690648954988513993793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24162460432636659009329195 36243690648954988513993793)
  ·
    refine ⟨27182767986716241385495345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36243690648954988513993793 27182767986716241385495345)
    ·
      refine ⟨20387075990037181039121509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27182767986716241385495345 20387075990037181039121509)
      ·
        refine ⟨3822576748131971444835283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20387075990037181039121509 3822576748131971444835283)
        ·
          refine ⟨5733865122197957167252925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3822576748131971444835283 5733865122197957167252925)
          ·
            refine ⟨2150199420824233937719847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5733865122197957167252925 2150199420824233937719847)
            ·
              refine ⟨3225299131236350906579771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150199420824233937719847 3225299131236350906579771)
              ·
                refine ⟨4837948696854526359869657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225299131236350906579771 4837948696854526359869657)
                ·
                  refine ⟨3628461522640894769902243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4837948696854526359869657 3628461522640894769902243)
                  ·
                    refine ⟨5442692283961342154853365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3628461522640894769902243 5442692283961342154853365)
                    ·
                      refine ⟨510252401621375827017503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5442692283961342154853365 510252401621375827017503)
                      ·
                        rfl

theorem cell23_993713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_993713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993713 prefixEnd_993713 := by exact prefixLift 993713
  have htrace : WordTrace (prefixWord ++ tailWord_993713) baseStart_993713 baseEnd_993713 := by
    simpa [prefixWord, tailWord_993713, baseEnd_993713] using wordTrace_append hprefix tailTrace_993713
  have hstable : (prefixWord ++ tailWord_993713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993713).length < 2 ^ (prefixWord ++ tailWord_993713).sum := by decide
  have hdescent : baseEnd_993713 < baseStart_993713 := by decide
  rcases family_descends (prefixWord ++ tailWord_993713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993820 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_993820 : Nat := 118140960795 + 993820 * 2 ^ 59
def prefixEnd_993820 : Nat := 4983230072969 + 3 ^ 40 * 993820 * 2
def baseEnd_993820 : Nat := 510307344051406908379511

theorem tailTrace_993820 : CollatzResearch.WordTrace tailWord_993820 prefixEnd_993820 510307344051406908379511 := by
  unfold tailWord_993820
  simp only [CollatzResearch.WordTrace]
  refine ⟨18123796629783672894069457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24165062173044897192092609 18123796629783672894069457)
  ·
    refine ⟨13592847472337754670552093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18123796629783672894069457 13592847472337754670552093)
    ·
      refine ⟨5097317802126658001457035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13592847472337754670552093 5097317802126658001457035)
      ·
        refine ⟨7645976703189987002185553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5097317802126658001457035 7645976703189987002185553)
        ·
          refine ⟨5734482527392490251639165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7645976703189987002185553 5734482527392490251639165)
          ·
            refine ⟨2150430947772183844364687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5734482527392490251639165 2150430947772183844364687)
            ·
              refine ⟨3225646421658275766547031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150430947772183844364687 3225646421658275766547031)
              ·
                refine ⟨4838469632487413649820547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225646421658275766547031 4838469632487413649820547)
                ·
                  refine ⟨7257704448731120474730821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838469632487413649820547 7257704448731120474730821)
                  ·
                    refine ⟨1360819584137085089012029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7257704448731120474730821 1360819584137085089012029)
                    ·
                      refine ⟨510307344051406908379511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1360819584137085089012029 510307344051406908379511)
                      ·
                        rfl

theorem cell23_993820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_993820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993820 prefixEnd_993820 := by exact prefixLift 993820
  have htrace : WordTrace (prefixWord ++ tailWord_993820) baseStart_993820 baseEnd_993820 := by
    simpa [prefixWord, tailWord_993820, baseEnd_993820] using wordTrace_append hprefix tailTrace_993820
  have hstable : (prefixWord ++ tailWord_993820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993820).length < 2 ^ (prefixWord ++ tailWord_993820).sum := by decide
  have hdescent : baseEnd_993820 < baseStart_993820 := by decide
  rcases family_descends (prefixWord ++ tailWord_993820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993827 : List Nat := [1, 1, 1, 4, 4, 1, 1, 5, 1, 4]
def baseStart_993827 : Nat := 118140960795 + 993827 * 2 ^ 59
def prefixEnd_993827 : Nat := 4983230072969 + 3 ^ 40 * 993827 * 2
def baseEnd_993827 : Nat := 170103646138662793663993

theorem tailTrace_993827 : CollatzResearch.WordTrace tailWord_993827 prefixEnd_993827 170103646138662793663993 := by
  unfold tailWord_993827
  simp only [CollatzResearch.WordTrace]
  refine ⟨36247848570541985983643735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24165232380361323989095823 36247848570541985983643735)
  ·
    refine ⟨54371772855812978975465603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36247848570541985983643735 54371772855812978975465603)
    ·
      refine ⟨81557659283719468463198405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54371772855812978975465603 81557659283719468463198405)
      ·
        refine ⟨15292061115697400336849701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81557659283719468463198405 15292061115697400336849701)
        ·
          refine ⟨2867261459193262563159319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15292061115697400336849701 2867261459193262563159319)
          ·
            refine ⟨4300892188789893844738979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867261459193262563159319 4300892188789893844738979)
            ·
              refine ⟨6451338283184840767108469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4300892188789893844738979 6451338283184840767108469)
              ·
                refine ⟨604812964048578821916419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6451338283184840767108469 604812964048578821916419)
                ·
                  refine ⟨907219446072868232874629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604812964048578821916419 907219446072868232874629)
                  ·
                    refine ⟨170103646138662793663993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 907219446072868232874629 170103646138662793663993)
                    ·
                      rfl

theorem cell23_993827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 4].length) (baseStart_993827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993827 prefixEnd_993827 := by exact prefixLift 993827
  have htrace : WordTrace (prefixWord ++ tailWord_993827) baseStart_993827 baseEnd_993827 := by
    simpa [prefixWord, tailWord_993827, baseEnd_993827] using wordTrace_append hprefix tailTrace_993827
  have hstable : (prefixWord ++ tailWord_993827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993827).length < 2 ^ (prefixWord ++ tailWord_993827).sum := by decide
  have hdescent : baseEnd_993827 < baseStart_993827 := by decide
  rcases family_descends (prefixWord ++ tailWord_993827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993857 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 6]
def baseStart_993857 : Nat := 118140960795 + 993857 * 2 ^ 59
def prefixEnd_993857 : Nat := 4983230072969 + 3 ^ 40 * 993857 * 2
def baseEnd_993857 : Nat := 56702926981735918179649

theorem tailTrace_993857 : CollatzResearch.WordTrace tailWord_993857 prefixEnd_993857 56702926981735918179649 := by
  unfold tailWord_993857
  simp only [CollatzResearch.WordTrace]
  refine ⟨36248942760433301107235825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24165961840288867404823883 36248942760433301107235825)
  ·
    refine ⟨27186707070324975830426869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36248942760433301107235825 27186707070324975830426869)
    ·
      refine ⟨2548753787842966484102519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27186707070324975830426869 2548753787842966484102519)
      ·
        refine ⟨3823130681764449726153779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2548753787842966484102519 3823130681764449726153779)
        ·
          refine ⟨5734696022646674589230669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823130681764449726153779 5734696022646674589230669)
          ·
            refine ⟨2150511008492502970961501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5734696022646674589230669 2150511008492502970961501)
            ·
              refine ⟨806441628184688614110563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2150511008492502970961501 806441628184688614110563)
              ·
                refine ⟨1209662442277032921165845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806441628184688614110563 1209662442277032921165845)
                ·
                  refine ⟨56702926981735918179649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1209662442277032921165845 56702926981735918179649)
                  ·
                    rfl

theorem cell23_993857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 6].length) (baseStart_993857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993857 prefixEnd_993857 := by exact prefixLift 993857
  have htrace : WordTrace (prefixWord ++ tailWord_993857) baseStart_993857 baseEnd_993857 := by
    simpa [prefixWord, tailWord_993857, baseEnd_993857] using wordTrace_append hprefix tailTrace_993857
  have hstable : (prefixWord ++ tailWord_993857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993857).length < 2 ^ (prefixWord ++ tailWord_993857).sum := by decide
  have hdescent : baseEnd_993857 < baseStart_993857 := by decide
  rcases family_descends (prefixWord ++ tailWord_993857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993870 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_993870 : Nat := 118140960795 + 993870 * 2 ^ 59
def prefixEnd_993870 : Nat := 4983230072969 + 3 ^ 40 * 993870 * 2
def baseEnd_993870 : Nat := 170111006028043904251427

theorem tailTrace_993870 : CollatzResearch.WordTrace tailWord_993870 prefixEnd_993870 170111006028043904251427 := by
  unfold tailWord_993870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4531177113673275540932383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24166277939590802884972709 4531177113673275540932383)
  ·
    refine ⟨6796765670509913311398575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4531177113673275540932383 6796765670509913311398575)
    ·
      refine ⟨10195148505764869967097863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6796765670509913311398575 10195148505764869967097863)
      ·
        refine ⟨15292722758647304950646795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10195148505764869967097863 15292722758647304950646795)
        ·
          refine ⟨22939084137970957425970193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15292722758647304950646795 22939084137970957425970193)
          ·
            refine ⟨17204313103478218069477645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22939084137970957425970193 17204313103478218069477645)
            ·
              refine ⟨6451617413804331776054117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17204313103478218069477645 6451617413804331776054117)
              ·
                refine ⟨1209678265088312208010147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6451617413804331776054117 1209678265088312208010147)
                ·
                  refine ⟨1814517397632468312015221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209678265088312208010147 1814517397632468312015221)
                  ·
                    refine ⟨170111006028043904251427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1814517397632468312015221 170111006028043904251427)
                    ·
                      rfl

theorem cell23_993870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_993870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993870 prefixEnd_993870 := by exact prefixLift 993870
  have htrace : WordTrace (prefixWord ++ tailWord_993870) baseStart_993870 baseEnd_993870 := by
    simpa [prefixWord, tailWord_993870, baseEnd_993870] using wordTrace_append hprefix tailTrace_993870
  have hstable : (prefixWord ++ tailWord_993870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993870).length < 2 ^ (prefixWord ++ tailWord_993870).sum := by decide
  have hdescent : baseEnd_993870 < baseStart_993870 := by decide
  rcases family_descends (prefixWord ++ tailWord_993870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993900 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_993900 : Nat := 118140960795 + 993900 * 2 ^ 59
def prefixEnd_993900 : Nat := 4983230072969 + 3 ^ 40 * 993900 * 2
def baseEnd_993900 : Nat := 170116140834588865126381

theorem tailTrace_993900 : CollatzResearch.WordTrace tailWord_993900 prefixEnd_993900 170116140834588865126381 := by
  unfold tailWord_993900
  simp only [CollatzResearch.WordTrace]
  refine ⟨18125255549638759725525577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24167007399518346300700769 18125255549638759725525577)
  ·
    refine ⟨13593941662229069794144183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18125255549638759725525577 13593941662229069794144183)
    ·
      refine ⟨20390912493343604691216275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13593941662229069794144183 20390912493343604691216275)
      ·
        refine ⟨30586368740015407036824413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20390912493343604691216275 30586368740015407036824413)
        ·
          refine ⟨11469888277505777638809155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30586368740015407036824413 11469888277505777638809155)
          ·
            refine ⟨17204832416258666458213733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11469888277505777638809155 17204832416258666458213733)
            ·
              refine ⟨3225906078048499960915075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17204832416258666458213733 3225906078048499960915075)
              ·
                refine ⟨4838859117072749941372613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225906078048499960915075 4838859117072749941372613)
                ·
                  refine ⟨907286084451140614007365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4838859117072749941372613 907286084451140614007365)
                  ·
                    refine ⟨170116140834588865126381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 907286084451140614007365 170116140834588865126381)
                    ·
                      rfl

theorem cell23_993900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_993900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993900 prefixEnd_993900 := by exact prefixLift 993900
  have htrace : WordTrace (prefixWord ++ tailWord_993900) baseStart_993900 baseEnd_993900 := by
    simpa [prefixWord, tailWord_993900, baseEnd_993900] using wordTrace_append hprefix tailTrace_993900
  have hstable : (prefixWord ++ tailWord_993900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993900).length < 2 ^ (prefixWord ++ tailWord_993900).sum := by decide
  have hdescent : baseEnd_993900 < baseStart_993900 := by decide
  rcases family_descends (prefixWord ++ tailWord_993900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993903 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_993903 : Nat := 118140960795 + 993903 * 2 ^ 59
def prefixEnd_993903 : Nat := 4983230072969 + 3 ^ 40 * 993903 * 2
def baseEnd_993903 : Nat := 510349962945730083641629

theorem tailTrace_993903 : CollatzResearch.WordTrace tailWord_993903 prefixEnd_993903 510349962945730083641629 := by
  unfold tailWord_993903
  simp only [CollatzResearch.WordTrace]
  refine ⟨36250620518266650963410363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24167080345511100642273575 36250620518266650963410363)
  ·
    refine ⟨54375930777399976445115545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36250620518266650963410363 54375930777399976445115545)
    ·
      refine ⟨40781948083049982333836659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54375930777399976445115545 40781948083049982333836659)
      ·
        refine ⟨61172922124574973500754989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40781948083049982333836659 61172922124574973500754989)
        ·
          refine ⟨22939845796715615062783121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61172922124574973500754989 22939845796715615062783121)
          ·
            refine ⟨17204884347536711297087341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22939845796715615062783121 17204884347536711297087341)
            ·
              refine ⟨6451831630326266736407753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17204884347536711297087341 6451831630326266736407753)
              ·
                refine ⟨4838873722744700052305815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451831630326266736407753 4838873722744700052305815)
                ·
                  refine ⟨7258310584117050078458723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838873722744700052305815 7258310584117050078458723)
                  ·
                    refine ⟨10887465876175575117688085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7258310584117050078458723 10887465876175575117688085)
                    ·
                      refine ⟨510349962945730083641629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10887465876175575117688085 510349962945730083641629)
                      ·
                        rfl

theorem cell23_993903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_993903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993903 prefixEnd_993903 := by exact prefixLift 993903
  have htrace : WordTrace (prefixWord ++ tailWord_993903) baseStart_993903 baseEnd_993903 := by
    simpa [prefixWord, tailWord_993903, baseEnd_993903] using wordTrace_append hprefix tailTrace_993903
  have hstable : (prefixWord ++ tailWord_993903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993903).length < 2 ^ (prefixWord ++ tailWord_993903).sum := by decide
  have hdescent : baseEnd_993903 < baseStart_993903 := by decide
  rcases family_descends (prefixWord ++ tailWord_993903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993907 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 3, 2, 2]
def baseStart_993907 : Nat := 118140960795 + 993907 * 2 ^ 59
def prefixEnd_993907 : Nat := 4983230072969 + 3 ^ 40 * 993907 * 2
def baseEnd_993907 : Nat := 510352016868348067991611

theorem tailTrace_993907 : CollatzResearch.WordTrace tailWord_993907 prefixEnd_993907 510352016868348067991611 := by
  unfold tailWord_993907
  simp only [CollatzResearch.WordTrace]
  refine ⟨36250766410252159646555975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24167177606834773097703983 36250766410252159646555975)
  ·
    refine ⟨54376149615378239469833963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36250766410252159646555975 54376149615378239469833963)
    ·
      refine ⟨81564224423067359204750945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54376149615378239469833963 81564224423067359204750945)
      ·
        refine ⟨61173168317300519403563209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81564224423067359204750945 61173168317300519403563209)
        ·
          refine ⟨45879876237975389552672407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61173168317300519403563209 45879876237975389552672407)
          ·
            refine ⟨68819814356963084329008611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45879876237975389552672407 68819814356963084329008611)
            ·
              refine ⟨103229721535444626493512917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68819814356963084329008611 103229721535444626493512917)
              ·
                refine ⟨2419446598486983433441709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103229721535444626493512917 2419446598486983433441709)
                ·
                  refine ⟨907292474432618787540641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2419446598486983433441709 907292474432618787540641)
                  ·
                    refine ⟨680469355824464090655481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 907292474432618787540641 680469355824464090655481)
                    ·
                      refine ⟨510352016868348067991611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 680469355824464090655481 510352016868348067991611)
                      ·
                        rfl

theorem cell23_993907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 2, 2].length) (baseStart_993907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993907 prefixEnd_993907 := by exact prefixLift 993907
  have htrace : WordTrace (prefixWord ++ tailWord_993907) baseStart_993907 baseEnd_993907 := by
    simpa [prefixWord, tailWord_993907, baseEnd_993907] using wordTrace_append hprefix tailTrace_993907
  have hstable : (prefixWord ++ tailWord_993907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993907).length < 2 ^ (prefixWord ++ tailWord_993907).sum := by decide
  have hdescent : baseEnd_993907 < baseStart_993907 := by decide
  rcases family_descends (prefixWord ++ tailWord_993907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993913 : List Nat := [1, 2, 1, 3, 3, 2, 1, 10]
def baseStart_993913 : Nat := 118140960795 + 993913 * 2 ^ 59
def prefixEnd_993913 : Nat := 4983230072969 + 3 ^ 40 * 993913 * 2
def baseEnd_993913 : Nat := 18902040657491668315429

theorem tailTrace_993913 : CollatzResearch.WordTrace tailWord_993913 prefixEnd_993913 18902040657491668315429 := by
  unfold tailWord_993913
  simp only [CollatzResearch.WordTrace]
  refine ⟨36250985248230422671274393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24167323498820281780849595 36250985248230422671274393)
  ·
    refine ⟨27188238936172817003455795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36250985248230422671274393 27188238936172817003455795)
    ·
      refine ⟨40782358404259225505183693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27188238936172817003455795 40782358404259225505183693)
      ·
        refine ⟨15293384401597209564443885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40782358404259225505183693 15293384401597209564443885)
        ·
          refine ⟨5735019150598953586666457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15293384401597209564443885 5735019150598953586666457)
          ·
            refine ⟨4301264362949215189999843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5735019150598953586666457 4301264362949215189999843)
            ·
              refine ⟨6451896544423822784999765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4301264362949215189999843 6451896544423822784999765)
              ·
                refine ⟨18902040657491668315429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6451896544423822784999765 18902040657491668315429)
                ·
                  rfl

theorem cell23_993913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 10].length) (baseStart_993913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993913 prefixEnd_993913 := by exact prefixLift 993913
  have htrace : WordTrace (prefixWord ++ tailWord_993913) baseStart_993913 baseEnd_993913 := by
    simpa [prefixWord, tailWord_993913, baseEnd_993913] using wordTrace_append hprefix tailTrace_993913
  have hstable : (prefixWord ++ tailWord_993913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993913).length < 2 ^ (prefixWord ++ tailWord_993913).sum := by decide
  have hdescent : baseEnd_993913 < baseStart_993913 := by decide
  rcases family_descends (prefixWord ++ tailWord_993913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993924 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_993924 : Nat := 118140960795 + 993924 * 2 ^ 59
def prefixEnd_993924 : Nat := 4983230072969 + 3 ^ 40 * 993924 * 2
def baseEnd_993924 : Nat := 510360746039474501479033

theorem tailTrace_993924 : CollatzResearch.WordTrace tailWord_993924 prefixEnd_993924 510360746039474501479033 := by
  unfold tailWord_993924
  simp only [CollatzResearch.WordTrace]
  refine ⟨18125693225595285774962413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24167590967460381033283217 18125693225595285774962413)
  ·
    refine ⟨6797134959598232165610905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18125693225595285774962413 6797134959598232165610905)
    ·
      refine ⟨5097851219698674124208179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6797134959598232165610905 5097851219698674124208179)
      ·
        refine ⟨7646776829548011186312269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5097851219698674124208179 7646776829548011186312269)
        ·
          refine ⟨2867541311080504194867101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7646776829548011186312269 2867541311080504194867101)
          ·
            refine ⟨1075327991655189073075163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2867541311080504194867101 1075327991655189073075163)
            ·
              refine ⟨1612991987482783609612745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075327991655189073075163 1612991987482783609612745)
              ·
                refine ⟨1209743990612087707209559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612991987482783609612745 1209743990612087707209559)
                ·
                  refine ⟨1814615985918131560814339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209743990612087707209559 1814615985918131560814339)
                  ·
                    refine ⟨2721923978877197341221509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1814615985918131560814339 2721923978877197341221509)
                    ·
                      refine ⟨510360746039474501479033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2721923978877197341221509 510360746039474501479033)
                      ·
                        rfl

theorem cell23_993924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_993924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993924 prefixEnd_993924 := by exact prefixLift 993924
  have htrace : WordTrace (prefixWord ++ tailWord_993924) baseStart_993924 baseEnd_993924 := by
    simpa [prefixWord, tailWord_993924, baseEnd_993924] using wordTrace_append hprefix tailTrace_993924
  have hstable : (prefixWord ++ tailWord_993924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993924).length < 2 ^ (prefixWord ++ tailWord_993924).sum := by decide
  have hdescent : baseEnd_993924 < baseStart_993924 := by decide
  rcases family_descends (prefixWord ++ tailWord_993924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993944 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 1, 2, 3]
def baseStart_993944 : Nat := 118140960795 + 993944 * 2 ^ 59
def prefixEnd_993944 : Nat := 4983230072969 + 3 ^ 40 * 993944 * 2
def baseEnd_993944 : Nat := 510371015652564423228941

theorem tailTrace_993944 : CollatzResearch.WordTrace tailWord_993944 prefixEnd_993944 510371015652564423228941 := by
  unfold tailWord_993944
  simp only [CollatzResearch.WordTrace]
  refine ⟨18126057955559057482826443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24168077274078743310435257 18126057955559057482826443)
  ·
    refine ⟨27189086933338586224239665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18126057955559057482826443 27189086933338586224239665)
    ·
      refine ⟨20391815200003939668179749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27189086933338586224239665 20391815200003939668179749)
      ·
        refine ⟨3823465350000738687783703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20391815200003939668179749 3823465350000738687783703)
        ·
          refine ⟨5735198025001108031675555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823465350000738687783703 5735198025001108031675555)
          ·
            refine ⟨8602797037501662047513333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735198025001108031675555 8602797037501662047513333)
            ·
              refine ⟨806512222265780816954375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8602797037501662047513333 806512222265780816954375)
              ·
                refine ⟨1209768333398671225431563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806512222265780816954375 1209768333398671225431563)
                ·
                  refine ⟨1814652500098006838147345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209768333398671225431563 1814652500098006838147345)
                  ·
                    refine ⟨1360989375073505128610509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1814652500098006838147345 1360989375073505128610509)
                    ·
                      refine ⟨510371015652564423228941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1360989375073505128610509 510371015652564423228941)
                      ·
                        rfl

theorem cell23_993944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_993944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993944 prefixEnd_993944 := by exact prefixLift 993944
  have htrace : WordTrace (prefixWord ++ tailWord_993944) baseStart_993944 baseEnd_993944 := by
    simpa [prefixWord, tailWord_993944, baseEnd_993944] using wordTrace_append hprefix tailTrace_993944
  have hstable : (prefixWord ++ tailWord_993944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993944).length < 2 ^ (prefixWord ++ tailWord_993944).sum := by decide
  have hdescent : baseEnd_993944 < baseStart_993944 := by decide
  rcases family_descends (prefixWord ++ tailWord_993944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993967 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 3, 3, 2]
def baseStart_993967 : Nat := 118140960795 + 993967 * 2 ^ 59
def prefixEnd_993967 : Nat := 4983230072969 + 3 ^ 40 * 993967 * 2
def baseEnd_993967 : Nat := 510382825707617833241335

theorem tailTrace_993967 : CollatzResearch.WordTrace tailWord_993967 prefixEnd_993967 510382825707617833241335 := by
  unfold tailWord_993967
  simp only [CollatzResearch.WordTrace]
  refine ⟨36252954790034789893740155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24168636526689859929160103 36252954790034789893740155)
  ·
    refine ⟨54379432185052184840610233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36252954790034789893740155 54379432185052184840610233)
    ·
      refine ⟨40784574138789138630457675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54379432185052184840610233 40784574138789138630457675)
      ·
        refine ⟨61176861208183707945686513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40784574138789138630457675 61176861208183707945686513)
        ·
          refine ⟨45882645906137780959264885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61176861208183707945686513 45882645906137780959264885)
          ·
            refine ⟨4301498053700416964931083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45882645906137780959264885 4301498053700416964931083)
            ·
              refine ⟨6452247080550625447396625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4301498053700416964931083 6452247080550625447396625)
              ·
                refine ⟨4839185310412969085547469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6452247080550625447396625 4839185310412969085547469)
                ·
                  refine ⟨1814694491404863407080301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4839185310412969085547469 1814694491404863407080301)
                  ·
                    refine ⟨680510434276823777655113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1814694491404863407080301 680510434276823777655113)
                    ·
                      refine ⟨510382825707617833241335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 680510434276823777655113 510382825707617833241335)
                      ·
                        rfl

theorem cell23_993967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 3, 2].length) (baseStart_993967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993967 prefixEnd_993967 := by exact prefixLift 993967
  have htrace : WordTrace (prefixWord ++ tailWord_993967) baseStart_993967 baseEnd_993967 := by
    simpa [prefixWord, tailWord_993967, baseEnd_993967] using wordTrace_append hprefix tailTrace_993967
  have hstable : (prefixWord ++ tailWord_993967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993967).length < 2 ^ (prefixWord ++ tailWord_993967).sum := by decide
  have hdescent : baseEnd_993967 < baseStart_993967 := by decide
  rcases family_descends (prefixWord ++ tailWord_993967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993980 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_993980 : Nat := 118140960795 + 993980 * 2 ^ 59
def prefixEnd_993980 : Nat := 4983230072969 + 3 ^ 40 * 993980 * 2
def baseEnd_993980 : Nat := 510389500956126282378775

theorem tailTrace_993980 : CollatzResearch.WordTrace tailWord_993980 prefixEnd_993980 510389500956126282378775 := by
  unfold tailWord_993980
  simp only [CollatzResearch.WordTrace]
  refine ⟨18126714469493846556981697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24168952625991795409308929 18126714469493846556981697)
  ·
    refine ⟨13595035852120384917736273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18126714469493846556981697 13595035852120384917736273)
    ·
      refine ⟨10196276889090288688302205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13595035852120384917736273 10196276889090288688302205)
      ·
        refine ⟨3823603833408858258113327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10196276889090288688302205 3823603833408858258113327)
        ·
          refine ⟨5735405750113287387169991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823603833408858258113327 5735405750113287387169991)
          ·
            refine ⟨8603108625169931080754987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735405750113287387169991 8603108625169931080754987)
            ·
              refine ⟨12904662937754896621132481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8603108625169931080754987 12904662937754896621132481)
              ·
                refine ⟨9678497203316172465849361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12904662937754896621132481 9678497203316172465849361)
                ·
                  refine ⟨7258872902487129349387021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9678497203316172465849361 7258872902487129349387021)
                  ·
                    refine ⟨2722077338432673506020133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7258872902487129349387021 2722077338432673506020133)
                    ·
                      refine ⟨510389500956126282378775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2722077338432673506020133 510389500956126282378775)
                      ·
                        rfl

theorem cell23_993980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_993980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993980 prefixEnd_993980 := by exact prefixLift 993980
  have htrace : WordTrace (prefixWord ++ tailWord_993980) baseStart_993980 baseEnd_993980 := by
    simpa [prefixWord, tailWord_993980, baseEnd_993980] using wordTrace_append hprefix tailTrace_993980
  have hstable : (prefixWord ++ tailWord_993980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993980).length < 2 ^ (prefixWord ++ tailWord_993980).sum := by decide
  have hdescent : baseEnd_993980 < baseStart_993980 := by decide
  rcases family_descends (prefixWord ++ tailWord_993980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994010 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_994010 : Nat := 118140960795 + 994010 * 2 ^ 59
def prefixEnd_994010 : Nat := 4983230072969 + 3 ^ 40 * 994010 * 2
def baseEnd_994010 : Nat := 510404905375761165003637

theorem tailTrace_994010 : CollatzResearch.WordTrace tailWord_994010 prefixEnd_994010 510404905375761165003637 := by
  unfold tailWord_994010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063630782219752059388871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24169682085919338825036989 9063630782219752059388871)
  ·
    refine ⟨13595446173329628089083307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9063630782219752059388871 13595446173329628089083307)
    ·
      refine ⟨20393169259994442133624961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13595446173329628089083307 20393169259994442133624961)
      ·
        refine ⟨15294876944995831600218721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20393169259994442133624961 15294876944995831600218721)
        ·
          refine ⟨11471157708746873700164041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15294876944995831600218721 11471157708746873700164041)
          ·
            refine ⟨8603368281560155275123031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11471157708746873700164041 8603368281560155275123031)
            ·
              refine ⟨12905052422340232912684547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8603368281560155275123031 12905052422340232912684547)
              ·
                refine ⟨19357578633510349369026821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12905052422340232912684547 19357578633510349369026821)
                ·
                  refine ⟨3629545993783190506692529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19357578633510349369026821 3629545993783190506692529)
                  ·
                    refine ⟨2722159495337392880019397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3629545993783190506692529 2722159495337392880019397)
                    ·
                      refine ⟨510404905375761165003637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2722159495337392880019397 510404905375761165003637)
                      ·
                        rfl

theorem cell23_994010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_994010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994010 prefixEnd_994010 := by exact prefixLift 994010
  have htrace : WordTrace (prefixWord ++ tailWord_994010) baseStart_994010 baseEnd_994010 := by
    simpa [prefixWord, tailWord_994010, baseEnd_994010] using wordTrace_append hprefix tailTrace_994010
  have hstable : (prefixWord ++ tailWord_994010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994010).length < 2 ^ (prefixWord ++ tailWord_994010).sum := by decide
  have hdescent : baseEnd_994010 < baseStart_994010 := by decide
  rcases family_descends (prefixWord ++ tailWord_994010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994020 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 7]
def baseStart_994020 : Nat := 118140960795 + 994020 * 2 ^ 59
def prefixEnd_994020 : Nat := 4983230072969 + 3 ^ 40 * 994020 * 2
def baseEnd_994020 : Nat := 56712226686922902875399

theorem tailTrace_994020 : CollatzResearch.WordTrace tailWord_994020 prefixEnd_994020 56712226686922902875399 := by
  unfold tailWord_994020
  simp only [CollatzResearch.WordTrace]
  refine ⟨18127443929421389972709757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24169925239228519963613009 18127443929421389972709757)
  ·
    refine ⟨6797791473533021239766159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18127443929421389972709757 6797791473533021239766159)
    ·
      refine ⟨10196687210299531859649239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6797791473533021239766159 10196687210299531859649239)
      ·
        refine ⟨15295030815449297789473859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10196687210299531859649239 15295030815449297789473859)
        ·
          refine ⟨22942546223173946684210789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15295030815449297789473859 22942546223173946684210789)
          ·
            refine ⟨4301727416845115003289523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22942546223173946684210789 4301727416845115003289523)
            ·
              refine ⟨6452591125267672504934285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4301727416845115003289523 6452591125267672504934285)
              ·
                refine ⟨2419721671975377189350357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6452591125267672504934285 2419721671975377189350357)
                ·
                  refine ⟨56712226686922902875399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2419721671975377189350357 56712226686922902875399)
                  ·
                    rfl

theorem cell23_994020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_994020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994020 prefixEnd_994020 := by exact prefixLift 994020
  have htrace : WordTrace (prefixWord ++ tailWord_994020) baseStart_994020 baseEnd_994020 := by
    simpa [prefixWord, tailWord_994020, baseEnd_994020] using wordTrace_append hprefix tailTrace_994020
  have hstable : (prefixWord ++ tailWord_994020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994020).length < 2 ^ (prefixWord ++ tailWord_994020).sum := by decide
  have hdescent : baseEnd_994020 < baseStart_994020 := by decide
  rcases family_descends (prefixWord ++ tailWord_994020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994060 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_994060 : Nat := 118140960795 + 994060 * 2 ^ 59
def prefixEnd_994060 : Nat := 4983230072969 + 3 ^ 40 * 994060 * 2
def baseEnd_994060 : Nat := 510430579408485969378407

theorem tailTrace_994060 : CollatzResearch.WordTrace tailWord_994060 prefixEnd_994060 510430579408485969378407 := by
  unfold tailWord_994060
  simp only [CollatzResearch.WordTrace]
  refine ⟨18128173389348933388437817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24170897852465244517917089 18128173389348933388437817)
  ·
    refine ⟨13596130042011700041328363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18128173389348933388437817 13596130042011700041328363)
    ·
      refine ⟨20394195063017550061992545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13596130042011700041328363 20394195063017550061992545)
      ·
        refine ⟨15295646297263162546494409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20394195063017550061992545 15295646297263162546494409)
        ·
          refine ⟨11471734722947371909870807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15295646297263162546494409 11471734722947371909870807)
          ·
            refine ⟨17207602084421057864806211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11471734722947371909870807 17207602084421057864806211)
            ·
              refine ⟨25811403126631586797209317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17207602084421057864806211 25811403126631586797209317)
              ·
                refine ⟨4839638086243422524476747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25811403126631586797209317 4839638086243422524476747)
                ·
                  refine ⟨7259457129365133786715121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839638086243422524476747 7259457129365133786715121)
                  ·
                    refine ⟨5444592847023850340036341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7259457129365133786715121 5444592847023850340036341)
                    ·
                      refine ⟨510430579408485969378407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5444592847023850340036341 510430579408485969378407)
                      ·
                        rfl

theorem cell23_994060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_994060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994060 prefixEnd_994060 := by exact prefixLift 994060
  have htrace : WordTrace (prefixWord ++ tailWord_994060) baseStart_994060 baseEnd_994060 := by
    simpa [prefixWord, tailWord_994060, baseEnd_994060] using wordTrace_append hprefix tailTrace_994060
  have hstable : (prefixWord ++ tailWord_994060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994060).length < 2 ^ (prefixWord ++ tailWord_994060).sum := by decide
  have hdescent : baseEnd_994060 < baseStart_994060 := by decide
  rcases family_descends (prefixWord ++ tailWord_994060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994071 : List Nat := [1, 1, 3, 4, 3, 1, 3, 2, 5]
def baseStart_994071 : Nat := 118140960795 + 994071 * 2 ^ 59
def prefixEnd_994071 : Nat := 4983230072969 + 3 ^ 40 * 994071 * 2
def baseEnd_994071 : Nat := 56715136410631714037873

theorem tailTrace_994071 : CollatzResearch.WordTrace tailWord_994071 prefixEnd_994071 56715136410631714037873 := by
  unfold tailWord_994071
  simp only [CollatzResearch.WordTrace]
  refine ⟨36256747981658015655526067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24171165321105343770350711 36256747981658015655526067)
  ·
    refine ⟨54385121972487023483289101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36256747981658015655526067 54385121972487023483289101)
    ·
      refine ⟨20394420739682633806233413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54385121972487023483289101 20394420739682633806233413)
      ·
        refine ⟨3823953888690493838668765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20394420739682633806233413 3823953888690493838668765)
        ·
          refine ⟨1433982708258935189500787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3823953888690493838668765 1433982708258935189500787)
          ·
            refine ⟨2150974062388402784251181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433982708258935189500787 2150974062388402784251181)
            ·
              refine ⟨806615273395651044094193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2150974062388402784251181 806615273395651044094193)
              ·
                refine ⟨604961455046738283070645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806615273395651044094193 604961455046738283070645)
                ·
                  refine ⟨56715136410631714037873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 604961455046738283070645 56715136410631714037873)
                  ·
                    rfl

theorem cell23_994071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 5].length) (baseStart_994071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994071 prefixEnd_994071 := by exact prefixLift 994071
  have htrace : WordTrace (prefixWord ++ tailWord_994071) baseStart_994071 baseEnd_994071 := by
    simpa [prefixWord, tailWord_994071, baseEnd_994071] using wordTrace_append hprefix tailTrace_994071
  have hstable : (prefixWord ++ tailWord_994071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994071).length < 2 ^ (prefixWord ++ tailWord_994071).sum := by decide
  have hdescent : baseEnd_994071 < baseStart_994071 := by decide
  rcases family_descends (prefixWord ++ tailWord_994071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994097 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 5, 4]
def baseStart_994097 : Nat := 118140960795 + 994097 * 2 ^ 59
def prefixEnd_994097 : Nat := 4983230072969 + 3 ^ 40 * 994097 * 2
def baseEnd_994097 : Nat := 170149859397567441538579

theorem tailTrace_994097 : CollatzResearch.WordTrace tailWord_994097 prefixEnd_994097 170149859397567441538579 := by
  unfold tailWord_994097
  simp only [CollatzResearch.WordTrace]
  refine ⟨36257696279563822095972545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24171797519709214730648363 36257696279563822095972545)
  ·
    refine ⟨27193272209672866571979409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36257696279563822095972545 27193272209672866571979409)
    ·
      refine ⟨20394954157254649928984557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27193272209672866571979409 20394954157254649928984557)
      ·
        refine ⟨7648107808970493723369209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20394954157254649928984557 7648107808970493723369209)
        ·
          refine ⟨5736080856727870292526907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7648107808970493723369209 5736080856727870292526907)
          ·
            refine ⟨8604121285091805438790361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736080856727870292526907 8604121285091805438790361)
            ·
              refine ⟨6453090963818854079092771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8604121285091805438790361 6453090963818854079092771)
              ·
                refine ⟨9679636445728281118639157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6453090963818854079092771 9679636445728281118639157)
                ·
                  refine ⟨907465916787026354872421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9679636445728281118639157 907465916787026354872421)
                  ·
                    refine ⟨170149859397567441538579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 907465916787026354872421 170149859397567441538579)
                    ·
                      rfl

theorem cell23_994097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_994097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994097 prefixEnd_994097 := by exact prefixLift 994097
  have htrace : WordTrace (prefixWord ++ tailWord_994097) baseStart_994097 baseEnd_994097 := by
    simpa [prefixWord, tailWord_994097, baseEnd_994097] using wordTrace_append hprefix tailTrace_994097
  have hstable : (prefixWord ++ tailWord_994097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994097).length < 2 ^ (prefixWord ++ tailWord_994097).sum := by decide
  have hdescent : baseEnd_994097 < baseStart_994097 := by decide
  rcases family_descends (prefixWord ++ tailWord_994097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994124 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_994124 : Nat := 118140960795 + 994124 * 2 ^ 59
def prefixEnd_994124 : Nat := 4983230072969 + 3 ^ 40 * 994124 * 2
def baseEnd_994124 : Nat := 510463442170373718978113

theorem tailTrace_994124 : CollatzResearch.WordTrace tailWord_994124 prefixEnd_994124 510463442170373718978113 := by
  unfold tailWord_994124
  simp only [CollatzResearch.WordTrace]
  refine ⟨18129340525233002853602713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24172454033644003804803617 18129340525233002853602713)
  ·
    refine ⟨13597005393924752140202035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18129340525233002853602713 13597005393924752140202035)
    ·
      refine ⟨20395508090887128210303053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13597005393924752140202035 20395508090887128210303053)
      ·
        refine ⟨7648315534082673078863645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20395508090887128210303053 7648315534082673078863645)
        ·
          refine ⟨2868118325281002404573867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7648315534082673078863645 2868118325281002404573867)
          ·
            refine ⟨4302177487921503606860801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868118325281002404573867 4302177487921503606860801)
            ·
              refine ⟨3226633115941127705145601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302177487921503606860801 3226633115941127705145601)
              ·
                refine ⟨2419974836955845778859201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226633115941127705145601 2419974836955845778859201)
                ·
                  refine ⟨1814981127716884334144401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2419974836955845778859201 1814981127716884334144401)
                  ·
                    refine ⟨1361235845787663250608301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1814981127716884334144401 1361235845787663250608301)
                    ·
                      refine ⟨510463442170373718978113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1361235845787663250608301 510463442170373718978113)
                      ·
                        rfl

theorem cell23_994124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_994124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994124 prefixEnd_994124 := by exact prefixLift 994124
  have htrace : WordTrace (prefixWord ++ tailWord_994124) baseStart_994124 baseEnd_994124 := by
    simpa [prefixWord, tailWord_994124, baseEnd_994124] using wordTrace_append hprefix tailTrace_994124
  have hstable : (prefixWord ++ tailWord_994124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994124).length < 2 ^ (prefixWord ++ tailWord_994124).sum := by decide
  have hdescent : baseEnd_994124 < baseStart_994124 := by decide
  rcases family_descends (prefixWord ++ tailWord_994124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994158 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_994158 : Nat := 118140960795 + 994158 * 2 ^ 59
def prefixEnd_994158 : Nat := 4983230072969 + 3 ^ 40 * 994158 * 2
def baseEnd_994158 : Nat := 510480900512626585952957

theorem tailTrace_994158 : CollatzResearch.WordTrace tailWord_994158 prefixEnd_994158 510480900512626585952957 := by
  unfold tailWord_994158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4532490141542853689242891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24173280754895219675962085 4532490141542853689242891)
  ·
    refine ⟨6798735212314280533864337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4532490141542853689242891 6798735212314280533864337)
    ·
      refine ⟨5099051409235710400398253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6798735212314280533864337 5099051409235710400398253)
      ·
        refine ⟨1912144278463391400149345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5099051409235710400398253 1912144278463391400149345)
        ·
          refine ⟨1434108208847543550112009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1912144278463391400149345 1434108208847543550112009)
          ·
            refine ⟨1075581156635657662584007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434108208847543550112009 1075581156635657662584007)
            ·
              refine ⟨1613371734953486493876011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075581156635657662584007 1613371734953486493876011)
              ·
                refine ⟨2420057602430229740814017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613371734953486493876011 2420057602430229740814017)
                ·
                  refine ⟨1815043201822672305610513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2420057602430229740814017 1815043201822672305610513)
                  ·
                    refine ⟨1361282401367004229207885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1815043201822672305610513 1361282401367004229207885)
                    ·
                      refine ⟨510480900512626585952957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1361282401367004229207885 510480900512626585952957)
                      ·
                        rfl

theorem cell23_994158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_994158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994158 prefixEnd_994158 := by exact prefixLift 994158
  have htrace : WordTrace (prefixWord ++ tailWord_994158) baseStart_994158 baseEnd_994158 := by
    simpa [prefixWord, tailWord_994158, baseEnd_994158] using wordTrace_append hprefix tailTrace_994158
  have hstable : (prefixWord ++ tailWord_994158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994158).length < 2 ^ (prefixWord ++ tailWord_994158).sum := by decide
  have hdescent : baseEnd_994158 < baseStart_994158 := by decide
  rcases family_descends (prefixWord ++ tailWord_994158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994171 : List Nat := [1, 1, 1, 1, 1, 5, 3, 5, 1, 1, 3]
def baseStart_994171 : Nat := 118140960795 + 994171 * 2 ^ 59
def prefixEnd_994171 : Nat := 4983230072969 + 3 ^ 40 * 994171 * 2
def baseEnd_994171 : Nat := 510487575761135035090397

theorem tailTrace_994171 : CollatzResearch.WordTrace tailWord_994171 prefixEnd_994171 510487575761135035090397 := by
  unfold tailWord_994171
  simp only [CollatzResearch.WordTrace]
  refine ⟨36260395281295732734166367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24173596854197155156110911 36260395281295732734166367)
  ·
    refine ⟨54390592921943599101249551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36260395281295732734166367 54390592921943599101249551)
    ·
      refine ⟨81585889382915398651874327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54390592921943599101249551 81585889382915398651874327)
      ·
        refine ⟨122378834074373097977811491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81585889382915398651874327 122378834074373097977811491)
        ·
          refine ⟨183568251111559646966717237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122378834074373097977811491 183568251111559646966717237)
          ·
            refine ⟨17209523541708716903129741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183568251111559646966717237 17209523541708716903129741)
            ·
              refine ⟨6453571328140768838673653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17209523541708716903129741 6453571328140768838673653)
              ·
                refine ⟨605022312013197078625655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6453571328140768838673653 605022312013197078625655)
                ·
                  refine ⟨907533468019795617938483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605022312013197078625655 907533468019795617938483)
                  ·
                    refine ⟨1361300202029693426907725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 907533468019795617938483 1361300202029693426907725)
                    ·
                      refine ⟨510487575761135035090397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1361300202029693426907725 510487575761135035090397)
                      ·
                        rfl

theorem cell23_994171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 1, 3].length) (baseStart_994171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994171 prefixEnd_994171 := by exact prefixLift 994171
  have htrace : WordTrace (prefixWord ++ tailWord_994171) baseStart_994171 baseEnd_994171 := by
    simpa [prefixWord, tailWord_994171, baseEnd_994171] using wordTrace_append hprefix tailTrace_994171
  have hstable : (prefixWord ++ tailWord_994171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994171).length < 2 ^ (prefixWord ++ tailWord_994171).sum := by decide
  have hdescent : baseEnd_994171 < baseStart_994171 := by decide
  rcases family_descends (prefixWord ++ tailWord_994171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994197 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_994197 : Nat := 118140960795 + 994197 * 2 ^ 59
def prefixEnd_994197 : Nat := 4983230072969 + 3 ^ 40 * 994197 * 2
def baseEnd_994197 : Nat := 510500926258151933365277

theorem tailTrace_994197 : CollatzResearch.WordTrace tailWord_994197 prefixEnd_994197 510500926258151933365277 := by
  unfold tailWord_994197
  simp only [CollatzResearch.WordTrace]
  refine ⟨36261343579201539174612845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24174229052801026116408563 36261343579201539174612845)
  ·
    refine ⟨13598003842200577190479817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36261343579201539174612845 13598003842200577190479817)
    ·
      refine ⟨10198502881650432892859863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13598003842200577190479817 10198502881650432892859863)
      ·
        refine ⟨15297754322475649339289795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10198502881650432892859863 15297754322475649339289795)
        ·
          refine ⟨22946631483713474008934693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15297754322475649339289795 22946631483713474008934693)
          ·
            refine ⟨4302493403196276376675255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22946631483713474008934693 4302493403196276376675255)
            ·
              refine ⟨6453740104794414565012883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302493403196276376675255 6453740104794414565012883)
              ·
                refine ⟨9680610157191621847519325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6453740104794414565012883 9680610157191621847519325)
                ·
                  refine ⟨3630228808946858192819747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9680610157191621847519325 3630228808946858192819747)
                  ·
                    refine ⟨5445343213420287289229621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3630228808946858192819747 5445343213420287289229621)
                    ·
                      refine ⟨510500926258151933365277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5445343213420287289229621 510500926258151933365277)
                      ·
                        rfl

theorem cell23_994197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_994197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994197 prefixEnd_994197 := by exact prefixLift 994197
  have htrace : WordTrace (prefixWord ++ tailWord_994197) baseStart_994197 baseEnd_994197 := by
    simpa [prefixWord, tailWord_994197, baseEnd_994197] using wordTrace_append hprefix tailTrace_994197
  have hstable : (prefixWord ++ tailWord_994197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994197).length < 2 ^ (prefixWord ++ tailWord_994197).sum := by decide
  have hdescent : baseEnd_994197 < baseStart_994197 := by decide
  rcases family_descends (prefixWord ++ tailWord_994197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994211 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 3, 2, 2]
def baseStart_994211 : Nat := 118140960795 + 994211 * 2 ^ 59
def prefixEnd_994211 : Nat := 4983230072969 + 3 ^ 40 * 994211 * 2
def baseEnd_994211 : Nat := 510508114987314878590213

theorem tailTrace_994211 : CollatzResearch.WordTrace tailWord_994211 prefixEnd_994211 510508114987314878590213 := by
  unfold tailWord_994211
  simp only [CollatzResearch.WordTrace]
  refine ⟨36261854201150819565622487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24174569467433879710414991 36261854201150819565622487)
  ·
    refine ⟨54392781301726229348433731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36261854201150819565622487 54392781301726229348433731)
    ·
      refine ⟨81589171952589344022650597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54392781301726229348433731 81589171952589344022650597)
      ·
        refine ⟨15297969741110502004246987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81589171952589344022650597 15297969741110502004246987)
        ·
          refine ⟨22946954611665753006370481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15297969741110502004246987 22946954611665753006370481)
          ·
            refine ⟨17210215958749314754777861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22946954611665753006370481 17210215958749314754777861)
            ·
              refine ⟨3226915492265496516520849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17210215958749314754777861 3226915492265496516520849)
              ·
                refine ⟨2420186619199122387390637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226915492265496516520849 2420186619199122387390637)
                ·
                  refine ⟨907569982199670895271489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2420186619199122387390637 907569982199670895271489)
                  ·
                    refine ⟨680677486649753171453617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 907569982199670895271489 680677486649753171453617)
                    ·
                      refine ⟨510508114987314878590213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 680677486649753171453617 510508114987314878590213)
                      ·
                        rfl

theorem cell23_994211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_994211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994211 prefixEnd_994211 := by exact prefixLift 994211
  have htrace : WordTrace (prefixWord ++ tailWord_994211) baseStart_994211 baseEnd_994211 := by
    simpa [prefixWord, tailWord_994211, baseEnd_994211] using wordTrace_append hprefix tailTrace_994211
  have hstable : (prefixWord ++ tailWord_994211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994211).length < 2 ^ (prefixWord ++ tailWord_994211).sum := by decide
  have hdescent : baseEnd_994211 < baseStart_994211 := by decide
  rcases family_descends (prefixWord ++ tailWord_994211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994228 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_994228 : Nat := 118140960795 + 994228 * 2 ^ 59
def prefixEnd_994228 : Nat := 4983230072969 + 3 ^ 40 * 994228 * 2
def baseEnd_994228 : Nat := 510516844158441312077635

theorem tailTrace_994228 : CollatzResearch.WordTrace tailWord_994228 prefixEnd_994228 510516844158441312077635 := by
  unfold tailWord_994228
  simp only [CollatzResearch.WordTrace]
  refine ⟨18131237121044615734495669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24174982828059487645994225 18131237121044615734495669)
  ·
    refine ⟨1699803480097932725108969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18131237121044615734495669 1699803480097932725108969)
    ·
      refine ⟨1274852610073449543831727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1699803480097932725108969 1274852610073449543831727)
      ·
        refine ⟨1912278915110174315747591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274852610073449543831727 1912278915110174315747591)
        ·
          refine ⟨2868418372665261473621387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912278915110174315747591 2868418372665261473621387)
          ·
            refine ⟨4302627558997892210432081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868418372665261473621387 4302627558997892210432081)
            ·
              refine ⟨3226970669248419157824061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302627558997892210432081 3226970669248419157824061)
              ·
                refine ⟨1210114000968157184184023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226970669248419157824061 1210114000968157184184023)
                ·
                  refine ⟨1815171001452235776276035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210114000968157184184023 1815171001452235776276035)
                  ·
                    refine ⟨2722756502178353664414053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1815171001452235776276035 2722756502178353664414053)
                    ·
                      refine ⟨510516844158441312077635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2722756502178353664414053 510516844158441312077635)
                      ·
                        rfl

theorem cell23_994228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_994228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994228 prefixEnd_994228 := by exact prefixLift 994228
  have htrace : WordTrace (prefixWord ++ tailWord_994228) baseStart_994228 baseEnd_994228 := by
    simpa [prefixWord, tailWord_994228, baseEnd_994228] using wordTrace_append hprefix tailTrace_994228
  have hstable : (prefixWord ++ tailWord_994228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994228).length < 2 ^ (prefixWord ++ tailWord_994228).sum := by decide
  have hdescent : baseEnd_994228 < baseStart_994228 := by decide
  rcases family_descends (prefixWord ++ tailWord_994228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994314 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_994314 : Nat := 118140960795 + 994314 * 2 ^ 59
def prefixEnd_994314 : Nat := 4983230072969 + 3 ^ 40 * 994314 * 2
def baseEnd_994314 : Nat := 510561003494727975602239

theorem tailTrace_994314 : CollatzResearch.WordTrace tailWord_994314 prefixEnd_994314 510561003494727975602239 := by
  unfold tailWord_994314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9066402729944417039155499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24177073946518445437747997 9066402729944417039155499)
  ·
    refine ⟨13599604094916625558733249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9066402729944417039155499 13599604094916625558733249)
    ·
      refine ⟨10199703071187469169049937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13599604094916625558733249 10199703071187469169049937)
      ·
        refine ⟨7649777303390601876787453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10199703071187469169049937 7649777303390601876787453)
        ·
          refine ⟨2868666488771475703795295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7649777303390601876787453 2868666488771475703795295)
          ·
            refine ⟨4302999733157213555692943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868666488771475703795295 4302999733157213555692943)
            ·
              refine ⟨6454499599735820333539415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302999733157213555692943 6454499599735820333539415)
              ·
                refine ⟨9681749399603730500309123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454499599735820333539415 9681749399603730500309123)
                ·
                  refine ⟨14522624099405595750463685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9681749399603730500309123 14522624099405595750463685)
                  ·
                    refine ⟨2722992018638549203211941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14522624099405595750463685 2722992018638549203211941)
                    ·
                      refine ⟨510561003494727975602239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2722992018638549203211941 510561003494727975602239)
                      ·
                        rfl

theorem cell23_994314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_994314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994314 prefixEnd_994314 := by exact prefixLift 994314
  have htrace : WordTrace (prefixWord ++ tailWord_994314) baseStart_994314 baseEnd_994314 := by
    simpa [prefixWord, tailWord_994314, baseEnd_994314] using wordTrace_append hprefix tailTrace_994314
  have hstable : (prefixWord ++ tailWord_994314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994314).length < 2 ^ (prefixWord ++ tailWord_994314).sum := by decide
  have hdescent : baseEnd_994314 < baseStart_994314 := by decide
  rcases family_descends (prefixWord ++ tailWord_994314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994318 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_994318 : Nat := 118140960795 + 994318 * 2 ^ 59
def prefixEnd_994318 : Nat := 4983230072969 + 3 ^ 40 * 994318 * 2
def baseEnd_994318 : Nat := 510563057417345959952221

theorem tailTrace_994318 : CollatzResearch.WordTrace tailWord_994318 prefixEnd_994318 510563057417345959952221 := by
  unfold tailWord_994318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4533219601470397104970951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24177171207842117893178405 4533219601470397104970951)
  ·
    refine ⟨6799829402205595657456427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4533219601470397104970951 6799829402205595657456427)
    ·
      refine ⟨10199744103308393486184641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6799829402205595657456427 10199744103308393486184641)
      ·
        refine ⟨7649808077481295114638481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10199744103308393486184641 7649808077481295114638481)
        ·
          refine ⟨5737356058110971335978861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7649808077481295114638481 5737356058110971335978861)
          ·
            refine ⟨2151508521791614250992073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5737356058110971335978861 2151508521791614250992073)
            ·
              refine ⟨1613631391343710688244055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151508521791614250992073 1613631391343710688244055)
              ·
                refine ⟨2420447087015566032366083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613631391343710688244055 2420447087015566032366083)
                ·
                  refine ⟨3630670630523349048549125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420447087015566032366083 3630670630523349048549125)
                  ·
                    refine ⟨680750743223127946602961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3630670630523349048549125 680750743223127946602961)
                    ·
                      refine ⟨510563057417345959952221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 680750743223127946602961 510563057417345959952221)
                      ·
                        rfl

theorem cell23_994318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_994318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994318 prefixEnd_994318 := by exact prefixLift 994318
  have htrace : WordTrace (prefixWord ++ tailWord_994318) baseStart_994318 baseEnd_994318 := by
    simpa [prefixWord, tailWord_994318, baseEnd_994318] using wordTrace_append hprefix tailTrace_994318
  have hstable : (prefixWord ++ tailWord_994318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994318).length < 2 ^ (prefixWord ++ tailWord_994318).sum := by decide
  have hdescent : baseEnd_994318 < baseStart_994318 := by decide
  rcases family_descends (prefixWord ++ tailWord_994318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994341 : List Nat := [1, 3, 1, 2, 2, 2, 4, 3, 5]
def baseStart_994341 : Nat := 118140960795 + 994341 * 2 ^ 59
def prefixEnd_994341 : Nat := 4983230072969 + 3 ^ 40 * 994341 * 2
def baseEnd_994341 : Nat := 56730540830266596662735

theorem tailTrace_994341 : CollatzResearch.WordTrace tailWord_994341 prefixEnd_994341 56730540830266596662735 := by
  unfold tailWord_994341
  simp only [CollatzResearch.WordTrace]
  refine ⟨36266595690679851767854877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24177730460453234511903251 36266595690679851767854877)
  ·
    refine ⟨13599973384004944412945579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36266595690679851767854877 13599973384004944412945579)
    ·
      refine ⟨20399960076007416619418369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13599973384004944412945579 20399960076007416619418369)
      ·
        refine ⟨15299970057005562464563777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20399960076007416619418369 15299970057005562464563777)
        ·
          refine ⟨11474977542754171848422833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15299970057005562464563777 11474977542754171848422833)
          ·
            refine ⟨8606233157065628886317125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11474977542754171848422833 8606233157065628886317125)
            ·
              refine ⟨1613668716949805416184461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8606233157065628886317125 1613668716949805416184461)
              ·
                refine ⟨605125768856177031069173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1613668716949805416184461 605125768856177031069173)
                ·
                  refine ⟨56730540830266596662735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605125768856177031069173 56730540830266596662735)
                  ·
                    rfl

theorem cell23_994341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_994341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994341 prefixEnd_994341 := by exact prefixLift 994341
  have htrace : WordTrace (prefixWord ++ tailWord_994341) baseStart_994341 baseEnd_994341 := by
    simpa [prefixWord, tailWord_994341, baseEnd_994341] using wordTrace_append hprefix tailTrace_994341
  have hstable : (prefixWord ++ tailWord_994341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994341).length < 2 ^ (prefixWord ++ tailWord_994341).sum := by decide
  have hdescent : baseEnd_994341 < baseStart_994341 := by decide
  rcases family_descends (prefixWord ++ tailWord_994341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994354 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_994354 : Nat := 118140960795 + 994354 * 2 ^ 59
def prefixEnd_994354 : Nat := 4983230072969 + 3 ^ 40 * 994354 * 2
def baseEnd_994354 : Nat := 170193847573635939700685

theorem tailTrace_994354 : CollatzResearch.WordTrace tailWord_994354 prefixEnd_994354 170193847573635939700685 := by
  unfold tailWord_994354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9066767459908188747019529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24178046559755169992052077 9066767459908188747019529)
  ·
    refine ⟨6800075594931141560264647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9066767459908188747019529 6800075594931141560264647)
    ·
      refine ⟨10200113392396712340396971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6800075594931141560264647 10200113392396712340396971)
      ·
        refine ⟨15300170088595068510595457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10200113392396712340396971 15300170088595068510595457)
        ·
          refine ⟨11475127566446301382946593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15300170088595068510595457 11475127566446301382946593)
          ·
            refine ⟨8606345674834726037209945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11475127566446301382946593 8606345674834726037209945)
            ·
              refine ⟨6454759256126044527907459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8606345674834726037209945 6454759256126044527907459)
              ·
                refine ⟨9682138884189066791861189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454759256126044527907459 9682138884189066791861189)
                ·
                  refine ⟨1815401040785450023473973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9682138884189066791861189 1815401040785450023473973)
                  ·
                    refine ⟨170193847573635939700685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1815401040785450023473973 170193847573635939700685)
                    ·
                      rfl

theorem cell23_994354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_994354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994354 prefixEnd_994354 := by exact prefixLift 994354
  have htrace : WordTrace (prefixWord ++ tailWord_994354) baseStart_994354 baseEnd_994354 := by
    simpa [prefixWord, tailWord_994354, baseEnd_994354] using wordTrace_append hprefix tailTrace_994354
  have hstable : (prefixWord ++ tailWord_994354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994354).length < 2 ^ (prefixWord ++ tailWord_994354).sum := by decide
  have hdescent : baseEnd_994354 < baseStart_994354 := by decide
  rcases family_descends (prefixWord ++ tailWord_994354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994358 : List Nat := [5, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_994358 : Nat := 118140960795 + 994358 * 2 ^ 59
def prefixEnd_994358 : Nat := 4983230072969 + 3 ^ 40 * 994358 * 2
def baseEnd_994358 : Nat := 56731510738169533716893

theorem tailTrace_994358 : CollatzResearch.WordTrace tailWord_994358 prefixEnd_994358 56731510738169533716893 := by
  unfold tailWord_994358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266700983226141479451483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24178143821078842447482485 2266700983226141479451483)
  ·
    refine ⟨3400051474839212219177225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2266700983226141479451483 3400051474839212219177225)
    ·
      refine ⟨2550038606129409164382919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3400051474839212219177225 2550038606129409164382919)
      ·
        refine ⟨3825057909194113746574379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550038606129409164382919 3825057909194113746574379)
        ·
          refine ⟨5737586863791170619861569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3825057909194113746574379 5737586863791170619861569)
          ·
            refine ⟨4303190147843377964896177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5737586863791170619861569 4303190147843377964896177)
            ·
              refine ⟨3227392610882533473672133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4303190147843377964896177 3227392610882533473672133)
              ·
                refine ⟨605136114540475026313525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3227392610882533473672133 605136114540475026313525)
                ·
                  refine ⟨56731510738169533716893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605136114540475026313525 56731510738169533716893)
                  ·
                    rfl

theorem cell23_994358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_994358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994358 prefixEnd_994358 := by exact prefixLift 994358
  have htrace : WordTrace (prefixWord ++ tailWord_994358) baseStart_994358 baseEnd_994358 := by
    simpa [prefixWord, tailWord_994358, baseEnd_994358] using wordTrace_append hprefix tailTrace_994358
  have hstable : (prefixWord ++ tailWord_994358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994358).length < 2 ^ (prefixWord ++ tailWord_994358).sum := by decide
  have hdescent : baseEnd_994358 < baseStart_994358 := by decide
  rcases family_descends (prefixWord ++ tailWord_994358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994451 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 1, 5, 2]
def baseStart_994451 : Nat := 118140960795 + 994451 * 2 ^ 59
def prefixEnd_994451 : Nat := 4983230072969 + 3 ^ 40 * 994451 * 2
def baseEnd_994451 : Nat := 510631350344393939589109

theorem tailTrace_994451 : CollatzResearch.WordTrace tailWord_994451 prefixEnd_994451 510631350344393939589109 := by
  unfold tailWord_994451
  simp only [CollatzResearch.WordTrace]
  refine ⟨36270607720281340554359207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24180405146854227036239471 36270607720281340554359207)
  ·
    refine ⟨54405911580422010831538811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36270607720281340554359207 54405911580422010831538811)
    ·
      refine ⟨81608867370633016247308217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54405911580422010831538811 81608867370633016247308217)
      ·
        refine ⟨61206650527974762185481163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81608867370633016247308217 61206650527974762185481163)
        ·
          refine ⟨91809975791962143278221745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61206650527974762185481163 91809975791962143278221745)
          ·
            refine ⟨68857481843971607458666309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91809975791962143278221745 68857481843971607458666309)
            ·
              refine ⟨12910777845744676398499933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68857481843971607458666309 12910777845744676398499933)
              ·
                refine ⟨4841541692154253649437475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12910777845744676398499933 4841541692154253649437475)
                ·
                  refine ⟨7262312538231380474156213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841541692154253649437475 7262312538231380474156213)
                  ·
                    refine ⟨680841800459191919452145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7262312538231380474156213 680841800459191919452145)
                    ·
                      refine ⟨510631350344393939589109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 680841800459191919452145 510631350344393939589109)
                      ·
                        rfl

theorem cell23_994451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 5, 2].length) (baseStart_994451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994451 prefixEnd_994451 := by exact prefixLift 994451
  have htrace : WordTrace (prefixWord ++ tailWord_994451) baseStart_994451 baseEnd_994451 := by
    simpa [prefixWord, tailWord_994451, baseEnd_994451] using wordTrace_append hprefix tailTrace_994451
  have hstable : (prefixWord ++ tailWord_994451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994451).length < 2 ^ (prefixWord ++ tailWord_994451).sum := by decide
  have hdescent : baseEnd_994451 < baseStart_994451 := by decide
  rcases family_descends (prefixWord ++ tailWord_994451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994504 : List Nat := [2, 1, 3, 1, 2, 1, 2, 11]
def baseStart_994504 : Nat := 118140960795 + 994504 * 2 ^ 59
def prefixEnd_994504 : Nat := 4983230072969 + 3 ^ 40 * 994504 * 2
def baseEnd_994504 : Nat := 18913280178484527119495

theorem tailTrace_994504 : CollatzResearch.WordTrace tailWord_994504 prefixEnd_994504 18913280178484527119495 := by
  unfold tailWord_994504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18136270394544665303019283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24181693859392887070692377 18136270394544665303019283)
  ·
    refine ⟨27204405591816997954528925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18136270394544665303019283 27204405591816997954528925)
    ·
      refine ⟨10201652096931374232948347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27204405591816997954528925 10201652096931374232948347)
      ·
        refine ⟨15302478145397061349422521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10201652096931374232948347 15302478145397061349422521)
        ·
          refine ⟨11476858609047796012066891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15302478145397061349422521 11476858609047796012066891)
          ·
            refine ⟨17215287913571694018100337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11476858609047796012066891 17215287913571694018100337)
            ·
              refine ⟨12911465935178770513575253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17215287913571694018100337 12911465935178770513575253)
              ·
                refine ⟨18913280178484527119495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 12911465935178770513575253 18913280178484527119495)
                ·
                  rfl

theorem cell23_994504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 11].length) (baseStart_994504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994504 prefixEnd_994504 := by exact prefixLift 994504
  have htrace : WordTrace (prefixWord ++ tailWord_994504) baseStart_994504 baseEnd_994504 := by
    simpa [prefixWord, tailWord_994504, baseEnd_994504] using wordTrace_append hprefix tailTrace_994504
  have hstable : (prefixWord ++ tailWord_994504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994504).length < 2 ^ (prefixWord ++ tailWord_994504).sum := by decide
  have hdescent : baseEnd_994504 < baseStart_994504 := by decide
  rcases family_descends (prefixWord ++ tailWord_994504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994525 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_994525 : Nat := 118140960795 + 994525 * 2 ^ 59
def prefixEnd_994525 : Nat := 4983230072969 + 3 ^ 40 * 994525 * 2
def baseEnd_994525 : Nat := 170223115970942216687923

theorem tailTrace_994525 : CollatzResearch.WordTrace tailWord_994525 prefixEnd_994525 170223115970942216687923 := by
  unfold tailWord_994525
  simp only [CollatzResearch.WordTrace]
  refine ⟨36273306722013251192553029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24182204481342167461702019 36273306722013251192553029)
  ·
    refine ⟨6801245010377484598603693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36273306722013251192553029 6801245010377484598603693)
    ·
      refine ⟨2550466878891556724476385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6801245010377484598603693 2550466878891556724476385)
      ·
        refine ⟨1912850159168667543357289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2550466878891556724476385 1912850159168667543357289)
        ·
          refine ⟨1434637619376500657517967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1912850159168667543357289 1434637619376500657517967)
          ·
            refine ⟨2151956429064750986276951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434637619376500657517967 2151956429064750986276951)
            ·
              refine ⟨3227934643597126479415427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151956429064750986276951 3227934643597126479415427)
              ·
                refine ⟨4841901965395689719123141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227934643597126479415427 4841901965395689719123141)
                ·
                  refine ⟨907856618511691822335589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4841901965395689719123141 907856618511691822335589)
                  ·
                    refine ⟨170223115970942216687923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 907856618511691822335589 170223115970942216687923)
                    ·
                      rfl

theorem cell23_994525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_994525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994525 prefixEnd_994525 := by exact prefixLift 994525
  have htrace : WordTrace (prefixWord ++ tailWord_994525) baseStart_994525 baseEnd_994525 := by
    simpa [prefixWord, tailWord_994525, baseEnd_994525] using wordTrace_append hprefix tailTrace_994525
  have hstable : (prefixWord ++ tailWord_994525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994525).length < 2 ^ (prefixWord ++ tailWord_994525).sum := by decide
  have hdescent : baseEnd_994525 < baseStart_994525 := by decide
  rcases family_descends (prefixWord ++ tailWord_994525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994532 : List Nat := [2, 3, 1, 1, 1, 2, 4, 4, 1, 2, 2]
def baseStart_994532 : Nat := 118140960795 + 994532 * 2 ^ 59
def prefixEnd_994532 : Nat := 4983230072969 + 3 ^ 40 * 994532 * 2
def baseEnd_994532 : Nat := 510672942277408122676237

theorem tailTrace_994532 : CollatzResearch.WordTrace tailWord_994532 prefixEnd_994532 510672942277408122676237 := by
  unfold tailWord_994532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18136781016493945694028925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24182374688658594258705233 18136781016493945694028925)
  ·
    refine ⟨6801292881185229635260847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18136781016493945694028925 6801292881185229635260847)
    ·
      refine ⟨10201939321777844452891271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6801292881185229635260847 10201939321777844452891271)
      ·
        refine ⟨15302908982666766679336907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10201939321777844452891271 15302908982666766679336907)
        ·
          refine ⟨22954363474000150019005361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15302908982666766679336907 22954363474000150019005361)
          ·
            refine ⟨17215772605500112514254021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22954363474000150019005361 17215772605500112514254021)
            ·
              refine ⟨3227957363531271096422629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17215772605500112514254021 3227957363531271096422629)
              ·
                refine ⟨605242005662113330579243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3227957363531271096422629 605242005662113330579243)
                ·
                  refine ⟨907863008493169995868865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605242005662113330579243 907863008493169995868865)
                  ·
                    refine ⟨680897256369877496901649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 907863008493169995868865 680897256369877496901649)
                    ·
                      refine ⟨510672942277408122676237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 680897256369877496901649 510672942277408122676237)
                      ·
                        rfl

theorem cell23_994532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_994532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994532 prefixEnd_994532 := by exact prefixLift 994532
  have htrace : WordTrace (prefixWord ++ tailWord_994532) baseStart_994532 baseEnd_994532 := by
    simpa [prefixWord, tailWord_994532, baseEnd_994532] using wordTrace_append hprefix tailTrace_994532
  have hstable : (prefixWord ++ tailWord_994532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994532).length < 2 ^ (prefixWord ++ tailWord_994532).sum := by decide
  have hdescent : baseEnd_994532 < baseStart_994532 := by decide
  rcases family_descends (prefixWord ++ tailWord_994532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994561 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_994561 : Nat := 118140960795 + 994561 * 2 ^ 59
def prefixEnd_994561 : Nat := 4983230072969 + 3 ^ 40 * 994561 * 2
def baseEnd_994561 : Nat := 510687833216388509213603

theorem tailTrace_994561 : CollatzResearch.WordTrace tailWord_994561 prefixEnd_994561 510687833216388509213603 := by
  unfold tailWord_994561
  simp only [CollatzResearch.WordTrace]
  refine ⟨36274619749882829340863537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24183079833255219560575691 36274619749882829340863537)
  ·
    refine ⟨27205964812412122005647653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36274619749882829340863537 27205964812412122005647653)
    ·
      refine ⟨5101118402327272876058935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27205964812412122005647653 5101118402327272876058935)
      ·
        refine ⟨7651677603490909314088403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5101118402327272876058935 7651677603490909314088403)
        ·
          refine ⟨11477516405236363971132605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7651677603490909314088403 11477516405236363971132605)
          ·
            refine ⟨4304068651963636489174727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11477516405236363971132605 4304068651963636489174727)
            ·
              refine ⟨6456102977945454733762091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4304068651963636489174727 6456102977945454733762091)
              ·
                refine ⟨9684154466918182100643137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6456102977945454733762091 9684154466918182100643137)
                ·
                  refine ⟨7263115850188636575482353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9684154466918182100643137 7263115850188636575482353)
                  ·
                    refine ⟨5447336887641477431611765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7263115850188636575482353 5447336887641477431611765)
                    ·
                      refine ⟨510687833216388509213603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5447336887641477431611765 510687833216388509213603)
                      ·
                        rfl

theorem cell23_994561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_994561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994561 prefixEnd_994561 := by exact prefixLift 994561
  have htrace : WordTrace (prefixWord ++ tailWord_994561) baseStart_994561 baseEnd_994561 := by
    simpa [prefixWord, tailWord_994561, baseEnd_994561] using wordTrace_append hprefix tailTrace_994561
  have hstable : (prefixWord ++ tailWord_994561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994561).length < 2 ^ (prefixWord ++ tailWord_994561).sum := by decide
  have hdescent : baseEnd_994561 < baseStart_994561 := by decide
  rcases family_descends (prefixWord ++ tailWord_994561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994638 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_994638 : Nat := 118140960795 + 994638 * 2 ^ 59
def prefixEnd_994638 : Nat := 4983230072969 + 3 ^ 40 * 994638 * 2
def baseEnd_994638 : Nat := 510727371226784707950749

theorem tailTrace_994638 : CollatzResearch.WordTrace tailWord_994638 prefixEnd_994638 510727371226784707950749 := by
  unfold tailWord_994638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534678521325483936427071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24184952113735914327611045 4534678521325483936427071)
  ·
    refine ⟨6802017781988225904640607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4534678521325483936427071 6802017781988225904640607)
    ·
      refine ⟨10203026672982338856960911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6802017781988225904640607 10203026672982338856960911)
      ·
        refine ⟨15304540009473508285441367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10203026672982338856960911 15304540009473508285441367)
        ·
          refine ⟨22956810014210262428162051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15304540009473508285441367 22956810014210262428162051)
          ·
            refine ⟨34435215021315393642243077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22956810014210262428162051 34435215021315393642243077)
            ·
              refine ⟨6456602816496636307920577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34435215021315393642243077 6456602816496636307920577)
              ·
                refine ⟨4842452112372477230940433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6456602816496636307920577 4842452112372477230940433)
                ·
                  refine ⟨3631839084279357923205325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4842452112372477230940433 3631839084279357923205325)
                  ·
                    refine ⟨1361939656604759221201997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3631839084279357923205325 1361939656604759221201997)
                    ·
                      refine ⟨510727371226784707950749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1361939656604759221201997 510727371226784707950749)
                      ·
                        rfl

theorem cell23_994638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_994638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994638 prefixEnd_994638 := by exact prefixLift 994638
  have htrace : WordTrace (prefixWord ++ tailWord_994638) baseStart_994638 baseEnd_994638 := by
    simpa [prefixWord, tailWord_994638, baseEnd_994638] using wordTrace_append hprefix tailTrace_994638
  have hstable : (prefixWord ++ tailWord_994638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994638).length < 2 ^ (prefixWord ++ tailWord_994638).sum := by decide
  have hdescent : baseEnd_994638 < baseStart_994638 := by decide
  rcases family_descends (prefixWord ++ tailWord_994638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994645 : List Nat := [1, 3, 2, 2, 3, 2, 1, 4, 5]
def baseStart_994645 : Nat := 118140960795 + 994645 * 2 ^ 59
def prefixEnd_994645 : Nat := 4983230072969 + 3 ^ 40 * 994645 * 2
def baseEnd_994645 : Nat := 56747885065707353395913

theorem tailTrace_994645 : CollatzResearch.WordTrace tailWord_994645 prefixEnd_994645 56747885065707353395913 := by
  unfold tailWord_994645
  simp only [CollatzResearch.WordTrace]
  refine ⟨36277683481578511686921389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24185122321052341124614259 36277683481578511686921389)
  ·
    refine ⟨13604131305591941882595521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36277683481578511686921389 13604131305591941882595521)
    ·
      refine ⟨10203098479193956411946641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13604131305591941882595521 10203098479193956411946641)
      ·
        refine ⟨7652323859395467308959981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10203098479193956411946641 7652323859395467308959981)
        ·
          refine ⟨2869621447273300240859993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7652323859395467308959981 2869621447273300240859993)
          ·
            refine ⟨2152216085454975180644995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2869621447273300240859993 2152216085454975180644995)
            ·
              refine ⟨3228324128182462770967493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152216085454975180644995 3228324128182462770967493)
              ·
                refine ⟨605310774034211769556405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3228324128182462770967493 605310774034211769556405)
                ·
                  refine ⟨56747885065707353395913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605310774034211769556405 56747885065707353395913)
                  ·
                    rfl

theorem cell23_994645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_994645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994645 prefixEnd_994645 := by exact prefixLift 994645
  have htrace : WordTrace (prefixWord ++ tailWord_994645) baseStart_994645 baseEnd_994645 := by
    simpa [prefixWord, tailWord_994645, baseEnd_994645] using wordTrace_append hprefix tailTrace_994645
  have hstable : (prefixWord ++ tailWord_994645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994645).length < 2 ^ (prefixWord ++ tailWord_994645).sum := by decide
  have hdescent : baseEnd_994645 < baseStart_994645 := by decide
  rcases family_descends (prefixWord ++ tailWord_994645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994648 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 1, 7, 2]
def baseStart_994648 : Nat := 118140960795 + 994648 * 2 ^ 59
def prefixEnd_994648 : Nat := 4983230072969 + 3 ^ 40 * 994648 * 2
def baseEnd_994648 : Nat := 510732506033329668825703

theorem tailTrace_994648 : CollatzResearch.WordTrace tailWord_994648 prefixEnd_994648 510732506033329668825703 := by
  unfold tailWord_994648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18138896450283821599640299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24185195267045095466187065 18138896450283821599640299)
  ·
    refine ⟨27208344675425732399460449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18138896450283821599640299 27208344675425732399460449)
    ·
      refine ⟨20406258506569299299595337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27208344675425732399460449 20406258506569299299595337)
      ·
        refine ⟨15304693879926974474696503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20406258506569299299595337 15304693879926974474696503)
        ·
          refine ⟨22957040819890461712044755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15304693879926974474696503 22957040819890461712044755)
          ·
            refine ⟨34435561229835692568067133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22957040819890461712044755 34435561229835692568067133)
            ·
              refine ⟨12913335461188384713025175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34435561229835692568067133 12913335461188384713025175)
              ·
                refine ⟨19370003191782577069537763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12913335461188384713025175 19370003191782577069537763)
                ·
                  refine ⟨29055004787673865604306645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19370003191782577069537763 29055004787673865604306645)
                  ·
                    refine ⟨680976674711106225100937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29055004787673865604306645 680976674711106225100937)
                    ·
                      refine ⟨510732506033329668825703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 680976674711106225100937 510732506033329668825703)
                      ·
                        rfl

theorem cell23_994648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_994648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994648 prefixEnd_994648 := by exact prefixLift 994648
  have htrace : WordTrace (prefixWord ++ tailWord_994648) baseStart_994648 baseEnd_994648 := by
    simpa [prefixWord, tailWord_994648, baseEnd_994648] using wordTrace_append hprefix tailTrace_994648
  have hstable : (prefixWord ++ tailWord_994648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994648).length < 2 ^ (prefixWord ++ tailWord_994648).sum := by decide
  have hdescent : baseEnd_994648 < baseStart_994648 := by decide
  rcases family_descends (prefixWord ++ tailWord_994648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994658 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_994658 : Nat := 118140960795 + 994658 * 2 ^ 59
def prefixEnd_994658 : Nat := 4983230072969 + 3 ^ 40 * 994658 * 2
def baseEnd_994658 : Nat := 170245880279958209900219

theorem tailTrace_994658 : CollatzResearch.WordTrace tailWord_994658 prefixEnd_994658 170245880279958209900219 := by
  unfold tailWord_994658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9069539407632853726786157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24185438420354276604763085 9069539407632853726786157)
  ·
    refine ⟨3401077277862320147544809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9069539407632853726786157 3401077277862320147544809)
    ·
      refine ⟨2550807958396740110658607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3401077277862320147544809 2550807958396740110658607)
      ·
        refine ⟨3826211937595110165987911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550807958396740110658607 3826211937595110165987911)
        ·
          refine ⟨5739317906392665248981867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826211937595110165987911 5739317906392665248981867)
          ·
            refine ⟨8608976859588997873472801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739317906392665248981867 8608976859588997873472801)
            ·
              refine ⟨6456732644691748405104601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8608976859588997873472801 6456732644691748405104601)
              ·
                refine ⟨4842549483518811303828451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6456732644691748405104601 4842549483518811303828451)
                ·
                  refine ⟨7263824225278216955742677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4842549483518811303828451 7263824225278216955742677)
                  ·
                    refine ⟨170245880279958209900219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7263824225278216955742677 170245880279958209900219)
                    ·
                      rfl

theorem cell23_994658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_994658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994658 prefixEnd_994658 := by exact prefixLift 994658
  have htrace : WordTrace (prefixWord ++ tailWord_994658) baseStart_994658 baseEnd_994658 := by
    simpa [prefixWord, tailWord_994658, baseEnd_994658] using wordTrace_append hprefix tailTrace_994658
  have hstable : (prefixWord ++ tailWord_994658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994658).length < 2 ^ (prefixWord ++ tailWord_994658).sum := by decide
  have hdescent : baseEnd_994658 < baseStart_994658 := by decide
  rcases family_descends (prefixWord ++ tailWord_994658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994695 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_994695 : Nat := 118140960795 + 994695 * 2 ^ 59
def prefixEnd_994695 : Nat := 4983230072969 + 3 ^ 40 * 994695 * 2
def baseEnd_994695 : Nat := 510756639624090984937987

theorem tailTrace_994695 : CollatzResearch.WordTrace tailWord_994695 prefixEnd_994695 510756639624090984937987 := by
  unfold tailWord_994695
  simp only [CollatzResearch.WordTrace]
  refine ⟨36279507131397370226241539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24186338087598246817494359 36279507131397370226241539)
  ·
    refine ⟨54419260697096055339362309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36279507131397370226241539 54419260697096055339362309)
    ·
      refine ⟨10203611380705510376130433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54419260697096055339362309 10203611380705510376130433)
      ·
        refine ⟨7652708535529132782097825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10203611380705510376130433 7652708535529132782097825)
        ·
          refine ⟨5739531401646849586573369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7652708535529132782097825 5739531401646849586573369)
          ·
            refine ⟨4304648551235137189930027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5739531401646849586573369 4304648551235137189930027)
            ·
              refine ⟨6456972826852705784895041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4304648551235137189930027 6456972826852705784895041)
              ·
                refine ⟨4842729620139529338671281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6456972826852705784895041 4842729620139529338671281)
                ·
                  refine ⟨3632047215104647004003461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4842729620139529338671281 3632047215104647004003461)
                  ·
                    refine ⟨681008852832121313250649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3632047215104647004003461 681008852832121313250649)
                    ·
                      refine ⟨510756639624090984937987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681008852832121313250649 510756639624090984937987)
                      ·
                        rfl

theorem cell23_994695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_994695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994695 prefixEnd_994695 := by exact prefixLift 994695
  have htrace : WordTrace (prefixWord ++ tailWord_994695) baseStart_994695 baseEnd_994695 := by
    simpa [prefixWord, tailWord_994695, baseEnd_994695] using wordTrace_append hprefix tailTrace_994695
  have hstable : (prefixWord ++ tailWord_994695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994695).length < 2 ^ (prefixWord ++ tailWord_994695).sum := by decide
  have hdescent : baseEnd_994695 < baseStart_994695 := by decide
  rcases family_descends (prefixWord ++ tailWord_994695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994755 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 4, 3, 2]
def baseStart_994755 : Nat := 118140960795 + 994755 * 2 ^ 59
def prefixEnd_994755 : Nat := 4983230072969 + 3 ^ 40 * 994755 * 2
def baseEnd_994755 : Nat := 510787448463360750187711

theorem tailTrace_994755 : CollatzResearch.WordTrace tailWord_994755 prefixEnd_994755 510787448463360750187711 := by
  unfold tailWord_994755
  simp only [CollatzResearch.WordTrace]
  refine ⟨36281695511180000473425719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24187797007453333648950479 36281695511180000473425719)
  ·
    refine ⟨54422543266770000710138579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36281695511180000473425719 54422543266770000710138579)
    ·
      refine ⟨81633814900155001065207869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54422543266770000710138579 81633814900155001065207869)
      ·
        refine ⟨30612680587558125399452951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81633814900155001065207869 30612680587558125399452951)
        ·
          refine ⟨45919020881337188099179427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30612680587558125399452951 45919020881337188099179427)
          ·
            refine ⟨68878531322005782148769141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45919020881337188099179427 68878531322005782148769141)
            ·
              refine ⟨6457362311438042076447107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68878531322005782148769141 6457362311438042076447107)
              ·
                refine ⟨9686043467157063114670661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457362311438042076447107 9686043467157063114670661)
                ·
                  refine ⟨1816133150091949334000749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9686043467157063114670661 1816133150091949334000749)
                  ·
                    refine ⟨681049931284481000250281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816133150091949334000749 681049931284481000250281)
                    ·
                      refine ⟨510787448463360750187711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681049931284481000250281 510787448463360750187711)
                      ·
                        rfl

theorem cell23_994755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_994755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994755 prefixEnd_994755 := by exact prefixLift 994755
  have htrace : WordTrace (prefixWord ++ tailWord_994755) baseStart_994755 baseEnd_994755 := by
    simpa [prefixWord, tailWord_994755, baseEnd_994755] using wordTrace_append hprefix tailTrace_994755
  have hstable : (prefixWord ++ tailWord_994755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994755).length < 2 ^ (prefixWord ++ tailWord_994755).sum := by decide
  have hdescent : baseEnd_994755 < baseStart_994755 := by decide
  rcases family_descends (prefixWord ++ tailWord_994755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994756 : List Nat := [2, 3, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_994756 : Nat := 118140960795 + 994756 * 2 ^ 59
def prefixEnd_994756 : Nat := 4983230072969 + 3 ^ 40 * 994756 * 2
def baseEnd_994756 : Nat := 170262653981338415425069

theorem tailTrace_994756 : CollatzResearch.WordTrace tailWord_994756 prefixEnd_994756 170262653981338415425069 := by
  unfold tailWord_994756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18140865992088188822106061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24187821322784251762808081 18140865992088188822106061)
  ·
    refine ⟨6802824747033070808289773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18140865992088188822106061 6802824747033070808289773)
    ·
      refine ⟨2551059280137401553108665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6802824747033070808289773 2551059280137401553108665)
      ·
        refine ⟨1913294460103051164831499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2551059280137401553108665 1913294460103051164831499)
        ·
          refine ⟨2869941690154576747247249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913294460103051164831499 2869941690154576747247249)
          ·
            refine ⟨2152456267615932560435437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2869941690154576747247249 2152456267615932560435437)
            ·
              refine ⟨807171100355974710163289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2152456267615932560435437 807171100355974710163289)
              ·
                refine ⟨605378325266981032622467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807171100355974710163289 605378325266981032622467)
                ·
                  refine ⟨908067487900471548933701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605378325266981032622467 908067487900471548933701)
                  ·
                    refine ⟨170262653981338415425069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 908067487900471548933701 170262653981338415425069)
                    ·
                      rfl

theorem cell23_994756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_994756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994756 prefixEnd_994756 := by exact prefixLift 994756
  have htrace : WordTrace (prefixWord ++ tailWord_994756) baseStart_994756 baseEnd_994756 := by
    simpa [prefixWord, tailWord_994756, baseEnd_994756] using wordTrace_append hprefix tailTrace_994756
  have hstable : (prefixWord ++ tailWord_994756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994756).length < 2 ^ (prefixWord ++ tailWord_994756).sum := by decide
  have hdescent : baseEnd_994756 < baseStart_994756 := by decide
  rcases family_descends (prefixWord ++ tailWord_994756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994762 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_994762 : Nat := 118140960795 + 994762 * 2 ^ 59
def prefixEnd_994762 : Nat := 4983230072969 + 3 ^ 40 * 994762 * 2
def baseEnd_994762 : Nat := 510791042827942222800179

theorem tailTrace_994762 : CollatzResearch.WordTrace tailWord_994762 prefixEnd_994762 510791042827942222800179 := by
  unfold tailWord_994762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9070487705538660167232635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24187967214769760445953693 9070487705538660167232635)
  ·
    refine ⟨13605731558307990250848953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9070487705538660167232635 13605731558307990250848953)
    ·
      refine ⟨10204298668730992688136715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13605731558307990250848953 10204298668730992688136715)
      ·
        refine ⟨15306448003096489032205073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10204298668730992688136715 15306448003096489032205073)
        ·
          refine ⟨11479836002322366774153805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15306448003096489032205073 11479836002322366774153805)
          ·
            refine ⟨4304938500870887540307677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11479836002322366774153805 4304938500870887540307677)
            ·
              refine ⟨1614351937826582827615379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4304938500870887540307677 1614351937826582827615379)
              ·
                refine ⟨2421527906739874241423069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614351937826582827615379 2421527906739874241423069)
                ·
                  refine ⟨908072965027452840533651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2421527906739874241423069 908072965027452840533651)
                  ·
                    refine ⟨1362109447541179260800477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 908072965027452840533651 1362109447541179260800477)
                    ·
                      refine ⟨510791042827942222800179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1362109447541179260800477 510791042827942222800179)
                      ·
                        rfl

theorem cell23_994762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_994762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994762 prefixEnd_994762 := by exact prefixLift 994762
  have htrace : WordTrace (prefixWord ++ tailWord_994762) baseStart_994762 baseEnd_994762 := by
    simpa [prefixWord, tailWord_994762, baseEnd_994762] using wordTrace_append hprefix tailTrace_994762
  have hstable : (prefixWord ++ tailWord_994762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994762).length < 2 ^ (prefixWord ++ tailWord_994762).sum := by decide
  have hdescent : baseEnd_994762 < baseStart_994762 := by decide
  rcases family_descends (prefixWord ++ tailWord_994762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994768 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_994768 : Nat := 118140960795 + 994768 * 2 ^ 59
def prefixEnd_994768 : Nat := 4983230072969 + 3 ^ 40 * 994768 * 2
def baseEnd_994768 : Nat := 510794123711869199325151

theorem tailTrace_994768 : CollatzResearch.WordTrace tailWord_994768 prefixEnd_994768 510794123711869199325151 := by
  unfold tailWord_994768
  simp only [CollatzResearch.WordTrace]
  refine ⟨18141084830066451846824479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24188113106755269129099305 18141084830066451846824479)
  ·
    refine ⟨27211627245099677770236719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18141084830066451846824479 27211627245099677770236719)
    ·
      refine ⟨40817440867649516655355079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27211627245099677770236719 40817440867649516655355079)
      ·
        refine ⟨61226161301474274983032619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40817440867649516655355079 61226161301474274983032619)
        ·
          refine ⟨91839241952211412474548929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61226161301474274983032619 91839241952211412474548929)
          ·
            refine ⟨68879431464158559355911697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91839241952211412474548929 68879431464158559355911697)
            ·
              refine ⟨51659573598118919516933773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68879431464158559355911697 51659573598118919516933773)
              ·
                refine ⟨19372340099294594818850165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51659573598118919516933773 19372340099294594818850165)
                ·
                  refine ⟨1816156884308868264267203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19372340099294594818850165 1816156884308868264267203)
                  ·
                    refine ⟨2724235326463302396400805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1816156884308868264267203 2724235326463302396400805)
                    ·
                      refine ⟨510794123711869199325151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2724235326463302396400805 510794123711869199325151)
                      ·
                        rfl

theorem cell23_994768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_994768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994768 prefixEnd_994768 := by exact prefixLift 994768
  have htrace : WordTrace (prefixWord ++ tailWord_994768) baseStart_994768 baseEnd_994768 := by
    simpa [prefixWord, tailWord_994768, baseEnd_994768] using wordTrace_append hprefix tailTrace_994768
  have hstable : (prefixWord ++ tailWord_994768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994768).length < 2 ^ (prefixWord ++ tailWord_994768).sum := by decide
  have hdescent : baseEnd_994768 < baseStart_994768 := by decide
  rcases family_descends (prefixWord ++ tailWord_994768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994785 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_994785 : Nat := 118140960795 + 994785 * 2 ^ 59
def prefixEnd_994785 : Nat := 4983230072969 + 3 ^ 40 * 994785 * 2
def baseEnd_994785 : Nat := 510802852882995632812573

theorem tailTrace_994785 : CollatzResearch.WordTrace tailWord_994785 prefixEnd_994785 510802852882995632812573 := by
  unfold tailWord_994785
  simp only [CollatzResearch.WordTrace]
  refine ⟨36282789701071315597017809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24188526467380877064678539 36282789701071315597017809)
  ·
    refine ⟨27212092275803486697763357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36282789701071315597017809 27212092275803486697763357)
    ·
      refine ⟨10204534603426307511661259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27212092275803486697763357 10204534603426307511661259)
      ·
        refine ⟨15306801905139461267491889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10204534603426307511661259 15306801905139461267491889)
        ·
          refine ⟨11480101428854595950618917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15306801905139461267491889 11480101428854595950618917)
          ·
            refine ⟨2152519017910236740741047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11480101428854595950618917 2152519017910236740741047)
            ·
              refine ⟨3228778526865355111111571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152519017910236740741047 3228778526865355111111571)
              ·
                refine ⟨4843167790298032666667357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3228778526865355111111571 4843167790298032666667357)
                ·
                  refine ⟨1816187921361762250000259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4843167790298032666667357 1816187921361762250000259)
                  ·
                    refine ⟨2724281882042643375000389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1816187921361762250000259 2724281882042643375000389)
                    ·
                      refine ⟨510802852882995632812573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2724281882042643375000389 510802852882995632812573)
                      ·
                        rfl

theorem cell23_994785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_994785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994785 prefixEnd_994785 := by exact prefixLift 994785
  have htrace : WordTrace (prefixWord ++ tailWord_994785) baseStart_994785 baseEnd_994785 := by
    simpa [prefixWord, tailWord_994785, baseEnd_994785] using wordTrace_append hprefix tailTrace_994785
  have hstable : (prefixWord ++ tailWord_994785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994785).length < 2 ^ (prefixWord ++ tailWord_994785).sum := by decide
  have hdescent : baseEnd_994785 < baseStart_994785 := by decide
  rcases family_descends (prefixWord ++ tailWord_994785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994788 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_994788 : Nat := 118140960795 + 994788 * 2 ^ 59
def prefixEnd_994788 : Nat := 4983230072969 + 3 ^ 40 * 994788 * 2
def baseEnd_994788 : Nat := 510804393324959121075059

theorem tailTrace_994788 : CollatzResearch.WordTrace tailWord_994788 prefixEnd_994788 510804393324959121075059 := by
  unfold tailWord_994788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18141449560030223554688509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24188599413373631406251345 18141449560030223554688509)
  ·
    refine ⟨6803043585011333833008191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18141449560030223554688509 6803043585011333833008191)
    ·
      refine ⟨10204565377517000749512287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6803043585011333833008191 10204565377517000749512287)
      ·
        refine ⟨15306848066275501124268431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10204565377517000749512287 15306848066275501124268431)
        ·
          refine ⟨22960272099413251686402647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15306848066275501124268431 22960272099413251686402647)
          ·
            refine ⟨34440408149119877529603971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22960272099413251686402647 34440408149119877529603971)
            ·
              refine ⟨51660612223679816294405957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34440408149119877529603971 51660612223679816294405957)
              ·
                refine ⟨9686364791939965555201117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51660612223679816294405957 9686364791939965555201117)
                ·
                  refine ⟨3632386796977487083200419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9686364791939965555201117 3632386796977487083200419)
                  ·
                    refine ⟨5448580195466230624800629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3632386796977487083200419 5448580195466230624800629)
                    ·
                      refine ⟨510804393324959121075059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5448580195466230624800629 510804393324959121075059)
                      ·
                        rfl

theorem cell23_994788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_994788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994788 prefixEnd_994788 := by exact prefixLift 994788
  have htrace : WordTrace (prefixWord ++ tailWord_994788) baseStart_994788 baseEnd_994788 := by
    simpa [prefixWord, tailWord_994788, baseEnd_994788] using wordTrace_append hprefix tailTrace_994788
  have hstable : (prefixWord ++ tailWord_994788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994788).length < 2 ^ (prefixWord ++ tailWord_994788).sum := by decide
  have hdescent : baseEnd_994788 < baseStart_994788 := by decide
  rcases family_descends (prefixWord ++ tailWord_994788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994789 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 2, 3, 2]
def baseStart_994789 : Nat := 118140960795 + 994789 * 2 ^ 59
def prefixEnd_994789 : Nat := 4983230072969 + 3 ^ 40 * 994789 * 2
def baseEnd_994789 : Nat := 510804906805613617162555

theorem tailTrace_994789 : CollatzResearch.WordTrace tailWord_994789 prefixEnd_994789 510804906805613617162555 := by
  unfold tailWord_994789
  simp only [CollatzResearch.WordTrace]
  refine ⟨36282935593056824280163421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24188623728704549520108947 36282935593056824280163421)
  ·
    refine ⟨13606100847396309105061283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36282935593056824280163421 13606100847396309105061283)
    ·
      refine ⟨20409151271094463657591925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13606100847396309105061283 20409151271094463657591925)
      ·
        refine ⟨1913357931665105967899243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20409151271094463657591925 1913357931665105967899243)
        ·
          refine ⟨2870036897497658951848865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913357931665105967899243 2870036897497658951848865)
          ·
            refine ⟨2152527673123244213886649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2870036897497658951848865 2152527673123244213886649)
            ·
              refine ⟨1614395754842433160414987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2152527673123244213886649 1614395754842433160414987)
              ·
                refine ⟨2421593632263649740622481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614395754842433160414987 2421593632263649740622481)
                ·
                  refine ⟨1816195224197737305466861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2421593632263649740622481 1816195224197737305466861)
                  ·
                    refine ⟨681073209074151489550073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816195224197737305466861 681073209074151489550073)
                    ·
                      refine ⟨510804906805613617162555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681073209074151489550073 510804906805613617162555)
                      ·
                        rfl

theorem cell23_994789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_994789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994789 prefixEnd_994789 := by exact prefixLift 994789
  have htrace : WordTrace (prefixWord ++ tailWord_994789) baseStart_994789 baseEnd_994789 := by
    simpa [prefixWord, tailWord_994789, baseEnd_994789] using wordTrace_append hprefix tailTrace_994789
  have hstable : (prefixWord ++ tailWord_994789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994789).length < 2 ^ (prefixWord ++ tailWord_994789).sum := by decide
  have hdescent : baseEnd_994789 < baseStart_994789 := by decide
  rcases family_descends (prefixWord ++ tailWord_994789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994835 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 3]
def baseStart_994835 : Nat := 118140960795 + 994835 * 2 ^ 59
def prefixEnd_994835 : Nat := 4983230072969 + 3 ^ 40 * 994835 * 2
def baseEnd_994835 : Nat := 510828526915720437187343

theorem tailTrace_994835 : CollatzResearch.WordTrace tailWord_994835 prefixEnd_994835 510828526915720437187343 := by
  unfold tailWord_994835
  simp only [CollatzResearch.WordTrace]
  refine ⟨36284613350890174136337959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24189742233926782757558639 36284613350890174136337959)
  ·
    refine ⟨54426920026335261204506939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36284613350890174136337959 54426920026335261204506939)
    ·
      refine ⟨81640380039502891806760409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54426920026335261204506939 81640380039502891806760409)
      ·
        refine ⟨61230285029627168855070307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81640380039502891806760409 61230285029627168855070307)
        ·
          refine ⟨91845427544440753282605461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61230285029627168855070307 91845427544440753282605461)
          ·
            refine ⟨4305254416145660310122131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91845427544440753282605461 4305254416145660310122131)
            ·
              refine ⟨6457881624218490465183197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305254416145660310122131 6457881624218490465183197)
              ·
                refine ⟨2421705609081933924443699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6457881624218490465183197 2421705609081933924443699)
                ·
                  refine ⟨3632558413622900886665549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421705609081933924443699 3632558413622900886665549)
                  ·
                    refine ⟨1362209405108587832499581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3632558413622900886665549 1362209405108587832499581)
                    ·
                      refine ⟨510828526915720437187343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1362209405108587832499581 510828526915720437187343)
                      ·
                        rfl

theorem cell23_994835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_994835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994835 prefixEnd_994835 := by exact prefixLift 994835
  have htrace : WordTrace (prefixWord ++ tailWord_994835) baseStart_994835 baseEnd_994835 := by
    simpa [prefixWord, tailWord_994835, baseEnd_994835] using wordTrace_append hprefix tailTrace_994835
  have hstable : (prefixWord ++ tailWord_994835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994835).length < 2 ^ (prefixWord ++ tailWord_994835).sum := by decide
  have hdescent : baseEnd_994835 < baseStart_994835 := by decide
  rcases family_descends (prefixWord ++ tailWord_994835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994869 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_994869 : Nat := 118140960795 + 994869 * 2 ^ 59
def prefixEnd_994869 : Nat := 4983230072969 + 3 ^ 40 * 994869 * 2
def baseEnd_994869 : Nat := 510845985257973304162187

theorem tailTrace_994869 : CollatzResearch.WordTrace tailWord_994869 prefixEnd_994869 510845985257973304162187 := by
  unfold tailWord_994869
  simp only [CollatzResearch.WordTrace]
  refine ⟨36285853432766997943075661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24190568955177998628717107 36285853432766997943075661)
  ·
    refine ⟨13607195037287624228653373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36285853432766997943075661 13607195037287624228653373)
    ·
      refine ⟨5102698138982859085745015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13607195037287624228653373 5102698138982859085745015)
      ·
        refine ⟨7654047208474288628617523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5102698138982859085745015 7654047208474288628617523)
        ·
          refine ⟨11481070812711432942926285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7654047208474288628617523 11481070812711432942926285)
          ·
            refine ⟨4305401554766787353597357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11481070812711432942926285 4305401554766787353597357)
            ·
              refine ⟨1614525583037545257599009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4305401554766787353597357 1614525583037545257599009)
              ·
                refine ⟨1210894187278158943199257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1614525583037545257599009 1210894187278158943199257)
                ·
                  refine ⟨908170640458619207399443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1210894187278158943199257 908170640458619207399443)
                  ·
                    refine ⟨1362255960687928811099165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 908170640458619207399443 1362255960687928811099165)
                    ·
                      refine ⟨510845985257973304162187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1362255960687928811099165 510845985257973304162187)
                      ·
                        rfl

theorem cell23_994869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_994869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994869 prefixEnd_994869 := by exact prefixLift 994869
  have htrace : WordTrace (prefixWord ++ tailWord_994869) baseStart_994869 baseEnd_994869 := by
    simpa [prefixWord, tailWord_994869, baseEnd_994869] using wordTrace_append hprefix tailTrace_994869
  have hstable : (prefixWord ++ tailWord_994869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994869).length < 2 ^ (prefixWord ++ tailWord_994869).sum := by decide
  have hdescent : baseEnd_994869 < baseStart_994869 := by decide
  rcases family_descends (prefixWord ++ tailWord_994869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994965 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_994965 : Nat := 118140960795 + 994965 * 2 ^ 59
def prefixEnd_994965 : Nat := 4983230072969 + 3 ^ 40 * 994965 * 2
def baseEnd_994965 : Nat := 510895279400804928561745

theorem tailTrace_994965 : CollatzResearch.WordTrace tailWord_994965 prefixEnd_994965 510895279400804928561745 := by
  unfold tailWord_994965
  simp only [CollatzResearch.WordTrace]
  refine ⟨36289354840419206338570349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24192903226946137559046899 36289354840419206338570349)
  ·
    refine ⟨13608508065157202376963881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36289354840419206338570349 13608508065157202376963881)
    ·
      refine ⟨10206381048867901782722911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13608508065157202376963881 10206381048867901782722911)
      ·
        refine ⟨15309571573301852674084367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10206381048867901782722911 15309571573301852674084367)
        ·
          refine ⟨22964357359952779011126551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15309571573301852674084367 22964357359952779011126551)
          ·
            refine ⟨34446536039929168516689827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22964357359952779011126551 34446536039929168516689827)
            ·
              refine ⟨51669804059893752775034741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34446536039929168516689827 51669804059893752775034741)
              ·
                refine ⟨4844044130615039322659507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51669804059893752775034741 4844044130615039322659507)
                ·
                  refine ⟨7266066195922558983989261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844044130615039322659507 7266066195922558983989261)
                  ·
                    refine ⟨2724774823470959618995973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7266066195922558983989261 2724774823470959618995973)
                    ·
                      refine ⟨510895279400804928561745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2724774823470959618995973 510895279400804928561745)
                      ·
                        rfl

theorem cell23_994965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_994965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994965 prefixEnd_994965 := by exact prefixLift 994965
  have htrace : WordTrace (prefixWord ++ tailWord_994965) baseStart_994965 baseEnd_994965 := by
    simpa [prefixWord, tailWord_994965, baseEnd_994965] using wordTrace_append hprefix tailTrace_994965
  have hstable : (prefixWord ++ tailWord_994965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994965).length < 2 ^ (prefixWord ++ tailWord_994965).sum := by decide
  have hdescent : baseEnd_994965 < baseStart_994965 := by decide
  rcases family_descends (prefixWord ++ tailWord_994965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994999 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 2, 4, 2]
def baseStart_994999 : Nat := 118140960795 + 994999 * 2 ^ 59
def prefixEnd_994999 : Nat := 4983230072969 + 3 ^ 40 * 994999 * 2
def baseEnd_994999 : Nat := 510912737743057795536589

theorem tailTrace_994999 : CollatzResearch.WordTrace tailWord_994999 prefixEnd_994999 510912737743057795536589 := by
  unfold tailWord_994999
  simp only [CollatzResearch.WordTrace]
  refine ⟨36290594922296030145308051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24193729948197353430205367 36290594922296030145308051)
  ·
    refine ⟨54435892383444045217962077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36290594922296030145308051 54435892383444045217962077)
    ·
      refine ⟨20413459643791516956735779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54435892383444045217962077 20413459643791516956735779)
      ·
        refine ⟨30620189465687275435103669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20413459643791516956735779 30620189465687275435103669)
        ·
          refine ⟨2870642762408182072040969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30620189465687275435103669 2870642762408182072040969)
          ·
            refine ⟨2152982071806136554030727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2870642762408182072040969 2152982071806136554030727)
            ·
              refine ⟨3229473107709204831046091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152982071806136554030727 3229473107709204831046091)
              ·
                refine ⟨4844209661563807246569137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229473107709204831046091 4844209661563807246569137)
                ·
                  refine ⟨3633157246172855434926853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4844209661563807246569137 3633157246172855434926853)
                  ·
                    refine ⟨681216983657410394048785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633157246172855434926853 681216983657410394048785)
                    ·
                      refine ⟨510912737743057795536589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681216983657410394048785 510912737743057795536589)
                      ·
                        rfl

theorem cell23_994999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_994999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_994999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_994999 prefixEnd_994999 := by exact prefixLift 994999
  have htrace : WordTrace (prefixWord ++ tailWord_994999) baseStart_994999 baseEnd_994999 := by
    simpa [prefixWord, tailWord_994999, baseEnd_994999] using wordTrace_append hprefix tailTrace_994999
  have hstable : (prefixWord ++ tailWord_994999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994999).length < 2 ^ (prefixWord ++ tailWord_994999).sum := by decide
  have hdescent : baseEnd_994999 < baseStart_994999 := by decide
  rcases family_descends (prefixWord ++ tailWord_994999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995026 : List Nat := [3, 2, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_995026 : Nat := 118140960795 + 995026 * 2 ^ 59
def prefixEnd_995026 : Nat := 4983230072969 + 3 ^ 40 * 995026 * 2
def baseEnd_995026 : Nat := 170308867240243063299655

theorem tailTrace_995026 : CollatzResearch.WordTrace tailWord_995026 prefixEnd_995026 170308867240243063299655 := by
  unfold tailWord_995026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9072894923299553439135233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24194386462132142504360621 9072894923299553439135233)
  ·
    refine ⟨6804671192474665079351425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9072894923299553439135233 6804671192474665079351425)
    ·
      refine ⟨5103503394355998809513569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6804671192474665079351425 5103503394355998809513569)
      ·
        refine ⟨3827627545766999107135177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5103503394355998809513569 3827627545766999107135177)
        ·
          refine ⟨2870720659325249330351383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3827627545766999107135177 2870720659325249330351383)
          ·
            refine ⟨4306080988987873995527075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870720659325249330351383 4306080988987873995527075)
            ·
              refine ⟨6459121483481810993290613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306080988987873995527075 6459121483481810993290613)
              ·
                refine ⟨605542639076419780620995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6459121483481810993290613 605542639076419780620995)
                ·
                  refine ⟨908313958614629670931493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605542639076419780620995 908313958614629670931493)
                  ·
                    refine ⟨170308867240243063299655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 908313958614629670931493 170308867240243063299655)
                    ·
                      rfl

theorem cell23_995026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_995026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995026 prefixEnd_995026 := by exact prefixLift 995026
  have htrace : WordTrace (prefixWord ++ tailWord_995026) baseStart_995026 baseEnd_995026 := by
    simpa [prefixWord, tailWord_995026, baseEnd_995026] using wordTrace_append hprefix tailTrace_995026
  have hstable : (prefixWord ++ tailWord_995026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995026).length < 2 ^ (prefixWord ++ tailWord_995026).sum := by decide
  have hdescent : baseEnd_995026 < baseStart_995026 := by decide
  rcases family_descends (prefixWord ++ tailWord_995026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995112 : List Nat := [2, 1, 5, 1, 1, 2, 1, 10]
def baseStart_995112 : Nat := 118140960795 + 995112 * 2 ^ 59
def prefixEnd_995112 : Nat := 4983230072969 + 3 ^ 40 * 995112 * 2
def baseEnd_995112 : Nat := 18924843002111698274947

theorem tailTrace_995112 : CollatzResearch.WordTrace tailWord_995112 prefixEnd_995112 18924843002111698274947 := by
  unfold tailWord_995112
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147358185443325222085795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24196477580591100296114393 18147358185443325222085795)
  ·
    refine ⟨27221037278164987833128693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18147358185443325222085795 27221037278164987833128693)
    ·
      refine ⟨2551972244827967609355815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27221037278164987833128693 2551972244827967609355815)
      ·
        refine ⟨3827958367241951414033723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551972244827967609355815 3827958367241951414033723)
        ·
          refine ⟨5741937550862927121050585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827958367241951414033723 5741937550862927121050585)
          ·
            refine ⟨4306453163147195340787939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5741937550862927121050585 4306453163147195340787939)
            ·
              refine ⟨6459679744720793011181909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306453163147195340787939 6459679744720793011181909)
              ·
                refine ⟨18924843002111698274947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6459679744720793011181909 18924843002111698274947)
                ·
                  rfl

theorem cell23_995112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 10].length) (baseStart_995112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995112 prefixEnd_995112 := by exact prefixLift 995112
  have htrace : WordTrace (prefixWord ++ tailWord_995112) baseStart_995112 baseEnd_995112 := by
    simpa [prefixWord, tailWord_995112, baseEnd_995112] using wordTrace_append hprefix tailTrace_995112
  have hstable : (prefixWord ++ tailWord_995112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995112).length < 2 ^ (prefixWord ++ tailWord_995112).sum := by decide
  have hdescent : baseEnd_995112 < baseStart_995112 := by decide
  rcases family_descends (prefixWord ++ tailWord_995112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995116 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_995116 : Nat := 118140960795 + 995116 * 2 ^ 59
def prefixEnd_995116 : Nat := 4983230072969 + 3 ^ 40 * 995116 * 2
def baseEnd_995116 : Nat := 170324271659877945924517

theorem tailTrace_995116 : CollatzResearch.WordTrace tailWord_995116 prefixEnd_995116 170324271659877945924517 := by
  unfold tailWord_995116
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147431131436079563658601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24196574841914772751544801 18147431131436079563658601)
  ·
    refine ⟨13610573348577059672743951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18147431131436079563658601 13610573348577059672743951)
    ·
      refine ⟨20415860022865589509115927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13610573348577059672743951 20415860022865589509115927)
      ·
        refine ⟨30623790034298384263673891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20415860022865589509115927 30623790034298384263673891)
        ·
          refine ⟨45935685051447576395510837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30623790034298384263673891 45935685051447576395510837)
          ·
            refine ⟨4306470473573210287079141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45935685051447576395510837 4306470473573210287079141)
            ·
              refine ⟨807463213794976928827339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4306470473573210287079141 807463213794976928827339)
              ·
                refine ⟨1211194820692465393241009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807463213794976928827339 1211194820692465393241009)
                ·
                  refine ⟨908396115519349044930757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1211194820692465393241009 908396115519349044930757)
                  ·
                    refine ⟨170324271659877945924517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 908396115519349044930757 170324271659877945924517)
                    ·
                      rfl

theorem cell23_995116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_995116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995116 prefixEnd_995116 := by exact prefixLift 995116
  have htrace : WordTrace (prefixWord ++ tailWord_995116) baseStart_995116 baseEnd_995116 := by
    simpa [prefixWord, tailWord_995116, baseEnd_995116] using wordTrace_append hprefix tailTrace_995116
  have hstable : (prefixWord ++ tailWord_995116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995116).length < 2 ^ (prefixWord ++ tailWord_995116).sum := by decide
  have hdescent : baseEnd_995116 < baseStart_995116 := by decide
  rcases family_descends (prefixWord ++ tailWord_995116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995123 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 1, 1, 4]
def baseStart_995123 : Nat := 118140960795 + 995123 * 2 ^ 59
def prefixEnd_995123 : Nat := 4983230072969 + 3 ^ 40 * 995123 * 2
def baseEnd_995123 : Nat := 510976409344215310386019

theorem tailTrace_995123 : CollatzResearch.WordTrace tailWord_995123 prefixEnd_995123 510976409344215310386019 := by
  unfold tailWord_995123
  simp only [CollatzResearch.WordTrace]
  refine ⟨36295117573846799322822023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24196745049231199548548015 36295117573846799322822023)
  ·
    refine ⟨54442676360770198984233035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36295117573846799322822023 54442676360770198984233035)
    ·
      refine ⟨81664014541155298476349553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54442676360770198984233035 81664014541155298476349553)
      ·
        refine ⟨61248010905866473857262165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81664014541155298476349553 61248010905866473857262165)
        ·
          refine ⟨717750127803122740514791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 61248010905866473857262165 717750127803122740514791)
          ·
            refine ⟨1076625191704684110772187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717750127803122740514791 1076625191704684110772187)
            ·
              refine ⟨1614937787557026166158281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076625191704684110772187 1614937787557026166158281)
              ·
                refine ⟨1211203340667769624618711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1614937787557026166158281 1211203340667769624618711)
                ·
                  refine ⟨1816805011001654436928067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211203340667769624618711 1816805011001654436928067)
                  ·
                    refine ⟨2725207516502481655392101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1816805011001654436928067 2725207516502481655392101)
                    ·
                      refine ⟨510976409344215310386019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2725207516502481655392101 510976409344215310386019)
                      ·
                        rfl

theorem cell23_995123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 1, 4].length) (baseStart_995123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995123 prefixEnd_995123 := by exact prefixLift 995123
  have htrace : WordTrace (prefixWord ++ tailWord_995123) baseStart_995123 baseEnd_995123 := by
    simpa [prefixWord, tailWord_995123, baseEnd_995123] using wordTrace_append hprefix tailTrace_995123
  have hstable : (prefixWord ++ tailWord_995123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995123).length < 2 ^ (prefixWord ++ tailWord_995123).sum := by decide
  have hdescent : baseEnd_995123 < baseStart_995123 := by decide
  rcases family_descends (prefixWord ++ tailWord_995123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995139 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 3]
def baseStart_995139 : Nat := 118140960795 + 995139 * 2 ^ 59
def prefixEnd_995139 : Nat := 4983230072969 + 3 ^ 40 * 995139 * 2
def baseEnd_995139 : Nat := 510984625034687247785945

theorem tailTrace_995139 : CollatzResearch.WordTrace tailWord_995139 prefixEnd_995139 510984625034687247785945 := by
  unfold tailWord_995139
  simp only [CollatzResearch.WordTrace]
  refine ⟨36295701141788834055404471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24197134094525889370269647 36295701141788834055404471)
  ·
    refine ⟨54443551712683251083106707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36295701141788834055404471 54443551712683251083106707)
    ·
      refine ⟨81665327569024876624660061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54443551712683251083106707 81665327569024876624660061)
      ·
        refine ⟨30624497838384328734247523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81665327569024876624660061 30624497838384328734247523)
        ·
          refine ⟨45936746757576493101371285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30624497838384328734247523 45936746757576493101371285)
          ·
            refine ⟨2153285004261398114126779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45936746757576493101371285 2153285004261398114126779)
            ·
              refine ⟨3229927506392097171190169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153285004261398114126779 3229927506392097171190169)
              ·
                refine ⟨2422445629794072878392627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229927506392097171190169 2422445629794072878392627)
                ·
                  refine ⟨3633668444691109317588941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422445629794072878392627 3633668444691109317588941)
                  ·
                    refine ⟨1362625666759165994095853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3633668444691109317588941 1362625666759165994095853)
                    ·
                      refine ⟨510984625034687247785945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1362625666759165994095853 510984625034687247785945)
                      ·
                        rfl

theorem cell23_995139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_995139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995139 prefixEnd_995139 := by exact prefixLift 995139
  have htrace : WordTrace (prefixWord ++ tailWord_995139) baseStart_995139 baseEnd_995139 := by
    simpa [prefixWord, tailWord_995139, baseEnd_995139] using wordTrace_append hprefix tailTrace_995139
  have hstable : (prefixWord ++ tailWord_995139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995139).length < 2 ^ (prefixWord ++ tailWord_995139).sum := by decide
  have hdescent : baseEnd_995139 < baseStart_995139 := by decide
  rcases family_descends (prefixWord ++ tailWord_995139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995157 : List Nat := [1, 3, 2, 2, 2, 4, 2, 2, 1, 2, 2]
def baseStart_995157 : Nat := 118140960795 + 995157 * 2 ^ 59
def prefixEnd_995157 : Nat := 4983230072969 + 3 ^ 40 * 995157 * 2
def baseEnd_995157 : Nat := 510993867686468177360863

theorem tailTrace_995157 : CollatzResearch.WordTrace tailWord_995157 prefixEnd_995157 510993867686468177360863 := by
  unfold tailWord_995157
  simp only [CollatzResearch.WordTrace]
  refine ⟨36296357655723623129559725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24197571770482415419706483 36296357655723623129559725)
  ·
    refine ⟨13611134120896358673584897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36296357655723623129559725 13611134120896358673584897)
    ·
      refine ⟨10208350590672269005188673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13611134120896358673584897 10208350590672269005188673)
      ·
        refine ⟨7656262943004201753891505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10208350590672269005188673 7656262943004201753891505)
        ·
          refine ⟨5742197207253151315418629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7656262943004201753891505 5742197207253151315418629)
          ·
            refine ⟨1076661976359965871640993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5742197207253151315418629 1076661976359965871640993)
            ·
              refine ⟨807496482269974403730745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076661976359965871640993 807496482269974403730745)
              ·
                refine ⟨605622361702480802798059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807496482269974403730745 605622361702480802798059)
                ·
                  refine ⟨908433542553721204197089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605622361702480802798059 908433542553721204197089)
                  ·
                    refine ⟨681325156915290903147817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 908433542553721204197089 681325156915290903147817)
                    ·
                      refine ⟨510993867686468177360863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681325156915290903147817 510993867686468177360863)
                      ·
                        rfl

theorem cell23_995157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_995157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995157 prefixEnd_995157 := by exact prefixLift 995157
  have htrace : WordTrace (prefixWord ++ tailWord_995157) baseStart_995157 baseEnd_995157 := by
    simpa [prefixWord, tailWord_995157, baseEnd_995157] using wordTrace_append hprefix tailTrace_995157
  have hstable : (prefixWord ++ tailWord_995157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995157).length < 2 ^ (prefixWord ++ tailWord_995157).sum := by decide
  have hdescent : baseEnd_995157 < baseStart_995157 := by decide
  rcases family_descends (prefixWord ++ tailWord_995157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995162 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_995162 : Nat := 118140960795 + 995162 * 2 ^ 59
def prefixEnd_995162 : Nat := 4983230072969 + 3 ^ 40 * 995162 * 2
def baseEnd_995162 : Nat := 510996435089740657798339

theorem tailTrace_995162 : CollatzResearch.WordTrace tailWord_995162 prefixEnd_995162 510996435089740657798339 := by
  unfold tailWord_995162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9074135005176377245872935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24197693347137005988994493 9074135005176377245872935)
  ·
    refine ⟨13611202507764565868809403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9074135005176377245872935 13611202507764565868809403)
    ·
      refine ⟨20416803761646848803214105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13611202507764565868809403 20416803761646848803214105)
      ·
        refine ⟨15312602821235136602410579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20416803761646848803214105 15312602821235136602410579)
        ·
          refine ⟨22968904231852704903615869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15312602821235136602410579 22968904231852704903615869)
          ·
            refine ⟨8613339086944764338855951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22968904231852704903615869 8613339086944764338855951)
            ·
              refine ⟨12920008630417146508283927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613339086944764338855951 12920008630417146508283927)
              ·
                refine ⟨19380012945625719762425891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12920008630417146508283927 19380012945625719762425891)
                ·
                  refine ⟨29070019418438579643638837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19380012945625719762425891 29070019418438579643638837)
                  ·
                    refine ⟨2725314320478616841591141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29070019418438579643638837 2725314320478616841591141)
                    ·
                      refine ⟨510996435089740657798339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2725314320478616841591141 510996435089740657798339)
                      ·
                        rfl

theorem cell23_995162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_995162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995162 prefixEnd_995162 := by exact prefixLift 995162
  have htrace : WordTrace (prefixWord ++ tailWord_995162) baseStart_995162 baseEnd_995162 := by
    simpa [prefixWord, tailWord_995162, baseEnd_995162] using wordTrace_append hprefix tailTrace_995162
  have hstable : (prefixWord ++ tailWord_995162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995162).length < 2 ^ (prefixWord ++ tailWord_995162).sum := by decide
  have hdescent : baseEnd_995162 < baseStart_995162 := by decide
  rcases family_descends (prefixWord ++ tailWord_995162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995249 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 1, 7]
def baseStart_995249 : Nat := 118140960795 + 995249 * 2 ^ 59
def prefixEnd_995249 : Nat := 4983230072969 + 3 ^ 40 * 995249 * 2
def baseEnd_995249 : Nat := 170347035968893939136813

theorem tailTrace_995249 : CollatzResearch.WordTrace tailWord_995249 prefixEnd_995249 170347035968893939136813 := by
  unfold tailWord_995249
  simp only [CollatzResearch.WordTrace]
  refine ⟨36299713171390322841908801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24199808780926881894605867 36299713171390322841908801)
  ·
    refine ⟨27224784878542742131431601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36299713171390322841908801 27224784878542742131431601)
    ·
      refine ⟨20418588658907056598573701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27224784878542742131431601 20418588658907056598573701)
      ·
        refine ⟨3828485373545073112232569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20418588658907056598573701 3828485373545073112232569)
        ·
          refine ⟨2871364030158804834174427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3828485373545073112232569 2871364030158804834174427)
          ·
            refine ⟨4307046045238207251261641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871364030158804834174427 4307046045238207251261641)
            ·
              refine ⟨3230284533928655438446231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4307046045238207251261641 3230284533928655438446231)
              ·
                refine ⟨4845426800892983157669347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230284533928655438446231 4845426800892983157669347)
                ·
                  refine ⟨7268140201339474736504021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845426800892983157669347 7268140201339474736504021)
                  ·
                    refine ⟨170347035968893939136813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7268140201339474736504021 170347035968893939136813)
                    ·
                      rfl

theorem cell23_995249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_995249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995249 prefixEnd_995249 := by exact prefixLift 995249
  have htrace : WordTrace (prefixWord ++ tailWord_995249) baseStart_995249 baseEnd_995249 := by
    simpa [prefixWord, tailWord_995249, baseEnd_995249] using wordTrace_append hprefix tailTrace_995249
  have hstable : (prefixWord ++ tailWord_995249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995249).length < 2 ^ (prefixWord ++ tailWord_995249).sum := by decide
  have hdescent : baseEnd_995249 < baseStart_995249 := by decide
  rcases family_descends (prefixWord ++ tailWord_995249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995253 : List Nat := [1, 3, 3, 2, 1, 4, 1, 3, 5]
def baseStart_995253 : Nat := 118140960795 + 995253 * 2 ^ 59
def prefixEnd_995253 : Nat := 4983230072969 + 3 ^ 40 * 995253 * 2
def baseEnd_995253 : Nat := 56782573536588866862269

theorem tailTrace_995253 : CollatzResearch.WordTrace tailWord_995253 prefixEnd_995253 56782573536588866862269 := by
  unfold tailWord_995253
  simp only [CollatzResearch.WordTrace]
  refine ⟨36299859063375831525054413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24199906042250554350036275 36299859063375831525054413)
  ·
    refine ⟨13612447148765936821895405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36299859063375831525054413 13612447148765936821895405)
    ·
      refine ⟨5104667680787226308210777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13612447148765936821895405 5104667680787226308210777)
      ·
        refine ⟨3828500760590419731158083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5104667680787226308210777 3828500760590419731158083)
        ·
          refine ⟨5742751140885629596737125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3828500760590419731158083 5742751140885629596737125)
          ·
            refine ⟨1076765838916055549388211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5742751140885629596737125 1076765838916055549388211)
            ·
              refine ⟨1615148758374083324082317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076765838916055549388211 1615148758374083324082317)
              ·
                refine ⟨605680784390281246530869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1615148758374083324082317 605680784390281246530869)
                ·
                  refine ⟨56782573536588866862269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605680784390281246530869 56782573536588866862269)
                  ·
                    rfl

theorem cell23_995253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_995253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995253 prefixEnd_995253 := by exact prefixLift 995253
  have htrace : WordTrace (prefixWord ++ tailWord_995253) baseStart_995253 baseEnd_995253 := by
    simpa [prefixWord, tailWord_995253, baseEnd_995253] using wordTrace_append hprefix tailTrace_995253
  have hstable : (prefixWord ++ tailWord_995253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995253).length < 2 ^ (prefixWord ++ tailWord_995253).sum := by decide
  have hdescent : baseEnd_995253 < baseStart_995253 := by decide
  rcases family_descends (prefixWord ++ tailWord_995253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995303 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_995303 : Nat := 118140960795 + 995303 * 2 ^ 59
def prefixEnd_995303 : Nat := 4983230072969 + 3 ^ 40 * 995303 * 2
def baseEnd_995303 : Nat := 511068835862024606135191

theorem tailTrace_995303 : CollatzResearch.WordTrace tailWord_995303 prefixEnd_995303 511068835862024606135191 := by
  unfold tailWord_995303
  simp only [CollatzResearch.WordTrace]
  refine ⟨36301682713194690064374563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24201121808796460042916375 36301682713194690064374563)
  ·
    refine ⟨54452524069792035096561845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36301682713194690064374563 54452524069792035096561845)
    ·
      refine ⟨5104924131543003290302673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54452524069792035096561845 5104924131543003290302673)
      ·
        refine ⟨3828693098657252467727005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5104924131543003290302673 3828693098657252467727005)
        ·
          refine ⟨1435759911996469675397627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3828693098657252467727005 1435759911996469675397627)
          ·
            refine ⟨2153639867994704513096441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435759911996469675397627 2153639867994704513096441)
            ·
              refine ⟨1615229900996028384822331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153639867994704513096441 1615229900996028384822331)
              ·
                refine ⟨2422844851494042577233497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615229900996028384822331 2422844851494042577233497)
                ·
                  refine ⟨1817133638620531932925123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2422844851494042577233497 1817133638620531932925123)
                  ·
                    refine ⟨2725700457930797899387685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1817133638620531932925123 2725700457930797899387685)
                    ·
                      refine ⟨511068835862024606135191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2725700457930797899387685 511068835862024606135191)
                      ·
                        rfl

theorem cell23_995303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_995303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995303 prefixEnd_995303 := by exact prefixLift 995303
  have htrace : WordTrace (prefixWord ++ tailWord_995303) baseStart_995303 baseEnd_995303 := by
    simpa [prefixWord, tailWord_995303, baseEnd_995303] using wordTrace_append hprefix tailTrace_995303
  have hstable : (prefixWord ++ tailWord_995303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995303).length < 2 ^ (prefixWord ++ tailWord_995303).sum := by decide
  have hdescent : baseEnd_995303 < baseStart_995303 := by decide
  rcases family_descends (prefixWord ++ tailWord_995303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995329 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_995329 : Nat := 118140960795 + 995329 * 2 ^ 59
def prefixEnd_995329 : Nat := 4983230072969 + 3 ^ 40 * 995329 * 2
def baseEnd_995329 : Nat := 511082186359041504410071

theorem tailTrace_995329 : CollatzResearch.WordTrace tailWord_995329 prefixEnd_995329 511082186359041504410071 := by
  unfold tailWord_995329
  simp only [CollatzResearch.WordTrace]
  refine ⟨36302631011100496504821041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24201754007400331003214027 36302631011100496504821041)
  ·
    refine ⟨27226973258325372378615781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36302631011100496504821041 27226973258325372378615781)
    ·
      refine ⟨5105057485936007320990459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27226973258325372378615781 5105057485936007320990459)
      ·
        refine ⟨7657586228904010981485689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5105057485936007320990459 7657586228904010981485689)
        ·
          refine ⟨5743189671678008236114267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7657586228904010981485689 5743189671678008236114267)
          ·
            refine ⟨8614784507517012354171401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743189671678008236114267 8614784507517012354171401)
            ·
              refine ⟨6461088380637759265628551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8614784507517012354171401 6461088380637759265628551)
              ·
                refine ⟨9691632570956638898442827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6461088380637759265628551 9691632570956638898442827)
                ·
                  refine ⟨14537448856434958347664241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9691632570956638898442827 14537448856434958347664241)
                  ·
                    refine ⟨10903086642326218760748181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14537448856434958347664241 10903086642326218760748181)
                    ·
                      refine ⟨511082186359041504410071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10903086642326218760748181 511082186359041504410071)
                      ·
                        rfl

theorem cell23_995329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_995329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995329 prefixEnd_995329 := by exact prefixLift 995329
  have htrace : WordTrace (prefixWord ++ tailWord_995329) baseStart_995329 baseEnd_995329 := by
    simpa [prefixWord, tailWord_995329, baseEnd_995329] using wordTrace_append hprefix tailTrace_995329
  have hstable : (prefixWord ++ tailWord_995329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995329).length < 2 ^ (prefixWord ++ tailWord_995329).sum := by decide
  have hdescent : baseEnd_995329 < baseStart_995329 := by decide
  rcases family_descends (prefixWord ++ tailWord_995329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995339 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 5, 5]
def baseStart_995339 : Nat := 118140960795 + 995339 * 2 ^ 59
def prefixEnd_995339 : Nat := 4983230072969 + 3 ^ 40 * 995339 * 2
def baseEnd_995339 : Nat := 170362440388528821761675

theorem tailTrace_995339 : CollatzResearch.WordTrace tailWord_995339 prefixEnd_995339 170362440388528821761675 := by
  unfold tailWord_995339
  simp only [CollatzResearch.WordTrace]
  refine ⟨36302995741064268212685071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24201997160709512141790047 36302995741064268212685071)
  ·
    refine ⟨54454493611596402319027607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36302995741064268212685071 54454493611596402319027607)
    ·
      refine ⟨81681740417394603478541411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54454493611596402319027607 81681740417394603478541411)
      ·
        refine ⟨122522610626091905217812117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81681740417394603478541411 122522610626091905217812117)
        ·
          refine ⟨5743247373098058057084943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122522610626091905217812117 5743247373098058057084943)
          ·
            refine ⟨8614871059647087085627415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743247373098058057084943 8614871059647087085627415)
            ·
              refine ⟨12922306589470630628441123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8614871059647087085627415 12922306589470630628441123)
              ·
                refine ⟨19383459884205945942661685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12922306589470630628441123 19383459884205945942661685)
                ·
                  refine ⟨1817199364144307432124533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19383459884205945942661685 1817199364144307432124533)
                  ·
                    refine ⟨170362440388528821761675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1817199364144307432124533 170362440388528821761675)
                    ·
                      rfl

theorem cell23_995339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 5].length) (baseStart_995339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995339 prefixEnd_995339 := by exact prefixLift 995339
  have htrace : WordTrace (prefixWord ++ tailWord_995339) baseStart_995339 baseEnd_995339 := by
    simpa [prefixWord, tailWord_995339, baseEnd_995339] using wordTrace_append hprefix tailTrace_995339
  have hstable : (prefixWord ++ tailWord_995339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995339).length < 2 ^ (prefixWord ++ tailWord_995339).sum := by decide
  have hdescent : baseEnd_995339 < baseStart_995339 := by decide
  rcases family_descends (prefixWord ++ tailWord_995339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995356 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_995356 : Nat := 118140960795 + 995356 * 2 ^ 59
def prefixEnd_995356 : Nat := 4983230072969 + 3 ^ 40 * 995356 * 2
def baseEnd_995356 : Nat := 170365350112237632924149

theorem tailTrace_995356 : CollatzResearch.WordTrace tailWord_995356 prefixEnd_995356 170365350112237632924149 := by
  unfold tailWord_995356
  simp only [CollatzResearch.WordTrace]
  refine ⟨18151807891001340058026961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24202410521335120077369281 18151807891001340058026961)
  ·
    refine ⟨13613855918251005043520221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18151807891001340058026961 13613855918251005043520221)
    ·
      refine ⟨5105195969344126891320083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13613855918251005043520221 5105195969344126891320083)
      ·
        refine ⟨7657793954016190336980125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5105195969344126891320083 7657793954016190336980125)
        ·
          refine ⟨2871672732756071376367547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7657793954016190336980125 2871672732756071376367547)
          ·
            refine ⟨4307509099134107064551321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871672732756071376367547 4307509099134107064551321)
            ·
              refine ⟨3230631824350580298413491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4307509099134107064551321 3230631824350580298413491)
              ·
                refine ⟨4845947736525870447620237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230631824350580298413491 4845947736525870447620237)
                ·
                  refine ⟨1817230401197201417857589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4845947736525870447620237 1817230401197201417857589)
                  ·
                    refine ⟨170365350112237632924149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1817230401197201417857589 170365350112237632924149)
                    ·
                      rfl

theorem cell23_995356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_995356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995356 prefixEnd_995356 := by exact prefixLift 995356
  have htrace : WordTrace (prefixWord ++ tailWord_995356) baseStart_995356 baseEnd_995356 := by
    simpa [prefixWord, tailWord_995356, baseEnd_995356] using wordTrace_append hprefix tailTrace_995356
  have hstable : (prefixWord ++ tailWord_995356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995356).length < 2 ^ (prefixWord ++ tailWord_995356).sum := by decide
  have hdescent : baseEnd_995356 < baseStart_995356 := by decide
  rcases family_descends (prefixWord ++ tailWord_995356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995399 : List Nat := [1, 1, 4, 1, 3, 1, 2, 10]
def baseStart_995399 : Nat := 118140960795 + 995399 * 2 ^ 59
def prefixEnd_995399 : Nat := 4983230072969 + 3 ^ 40 * 995399 * 2
def baseEnd_995399 : Nat := 18930301111290971501287

theorem tailTrace_995399 : CollatzResearch.WordTrace tailWord_995399 prefixEnd_995399 18930301111290971501287 := by
  unfold tailWord_995399
  simp only [CollatzResearch.WordTrace]
  refine ⟨36305184120846898459869251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24203456080564598973246167 36305184120846898459869251)
  ·
    refine ⟨54457776181270347689803877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36305184120846898459869251 54457776181270347689803877)
    ·
      refine ⟨10210833033988190191838227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54457776181270347689803877 10210833033988190191838227)
      ·
        refine ⟨15316249550982285287757341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210833033988190191838227 15316249550982285287757341)
        ·
          refine ⟨5743593581618356982909003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15316249550982285287757341 5743593581618356982909003)
          ·
            refine ⟨8615390372427535474363505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743593581618356982909003 8615390372427535474363505)
            ·
              refine ⟨6461542779320651605772629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8615390372427535474363505 6461542779320651605772629)
              ·
                refine ⟨18930301111290971501287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6461542779320651605772629 18930301111290971501287)
                ·
                  rfl

theorem cell23_995399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 10].length) (baseStart_995399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995399 prefixEnd_995399 := by exact prefixLift 995399
  have htrace : WordTrace (prefixWord ++ tailWord_995399) baseStart_995399 baseEnd_995399 := by
    simpa [prefixWord, tailWord_995399, baseEnd_995399] using wordTrace_append hprefix tailTrace_995399
  have hstable : (prefixWord ++ tailWord_995399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995399).length < 2 ^ (prefixWord ++ tailWord_995399).sum := by decide
  have hdescent : baseEnd_995399 < baseStart_995399 := by decide
  rcases family_descends (prefixWord ++ tailWord_995399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995406 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_995406 : Nat := 118140960795 + 995406 * 2 ^ 59
def prefixEnd_995406 : Nat := 4983230072969 + 3 ^ 40 * 995406 * 2
def baseEnd_995406 : Nat := 511121724369437703147217

theorem tailTrace_995406 : CollatzResearch.WordTrace tailWord_995406 prefixEnd_995406 511121724369437703147217 := by
  unfold tailWord_995406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4538179928977692331921759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24203626287881025770249381 4538179928977692331921759)
  ·
    refine ⟨6807269893466538497882639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4538179928977692331921759 6807269893466538497882639)
    ·
      refine ⟨10210904840199807746823959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6807269893466538497882639 10210904840199807746823959)
      ·
        refine ⟨15316357260299711620235939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210904840199807746823959 15316357260299711620235939)
        ·
          refine ⟨22974535890449567430353909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15316357260299711620235939 22974535890449567430353909)
          ·
            refine ⟨2153862739729646946595679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22974535890449567430353909 2153862739729646946595679)
            ·
              refine ⟨3230794109594470419893519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153862739729646946595679 3230794109594470419893519)
              ·
                refine ⟨4846191164391705629840279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230794109594470419893519 4846191164391705629840279)
                ·
                  refine ⟨7269286746587558444760419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846191164391705629840279 7269286746587558444760419)
                  ·
                    refine ⟨10903930119881337667140629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7269286746587558444760419 10903930119881337667140629)
                    ·
                      refine ⟨511121724369437703147217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10903930119881337667140629 511121724369437703147217)
                      ·
                        rfl

theorem cell23_995406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_995406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995406 prefixEnd_995406 := by exact prefixLift 995406
  have htrace : WordTrace (prefixWord ++ tailWord_995406) baseStart_995406 baseEnd_995406 := by
    simpa [prefixWord, tailWord_995406, baseEnd_995406] using wordTrace_append hprefix tailTrace_995406
  have hstable : (prefixWord ++ tailWord_995406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995406).length < 2 ^ (prefixWord ++ tailWord_995406).sum := by decide
  have hdescent : baseEnd_995406 < baseStart_995406 := by decide
  rcases family_descends (prefixWord ++ tailWord_995406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995410 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_995410 : Nat := 118140960795 + 995410 * 2 ^ 59
def prefixEnd_995410 : Nat := 4983230072969 + 3 ^ 40 * 995410 * 2
def baseEnd_995410 : Nat := 511123778292055687497199

theorem tailTrace_995410 : CollatzResearch.WordTrace tailWord_995410 prefixEnd_995410 511123778292055687497199 := by
  unfold tailWord_995410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076396330951761834629921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24203723549204698225679789 9076396330951761834629921)
  ·
    refine ⟨6807297248213821375972441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9076396330951761834629921 6807297248213821375972441)
    ·
      refine ⟨5105472936160366031979331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6807297248213821375972441 5105472936160366031979331)
      ·
        refine ⟨7658209404240549047968997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5105472936160366031979331 7658209404240549047968997)
        ·
          refine ⟨1435914263295102946494187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7658209404240549047968997 1435914263295102946494187)
          ·
            refine ⟨2153871394942654419741281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435914263295102946494187 2153871394942654419741281)
            ·
              refine ⟨1615403546206990814805961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153871394942654419741281 1615403546206990814805961)
              ·
                refine ⟨1211552659655243111104471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615403546206990814805961 1211552659655243111104471)
                ·
                  refine ⟨1817328989482864666656707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211552659655243111104471 1817328989482864666656707)
                  ·
                    refine ⟨2725993484224296999985061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1817328989482864666656707 2725993484224296999985061)
                    ·
                      refine ⟨511123778292055687497199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2725993484224296999985061 511123778292055687497199)
                      ·
                        rfl

theorem cell23_995410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_995410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995410 prefixEnd_995410 := by exact prefixLift 995410
  have htrace : WordTrace (prefixWord ++ tailWord_995410) baseStart_995410 baseEnd_995410 := by
    simpa [prefixWord, tailWord_995410, baseEnd_995410] using wordTrace_append hprefix tailTrace_995410
  have hstable : (prefixWord ++ tailWord_995410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995410).length < 2 ^ (prefixWord ++ tailWord_995410).sum := by decide
  have hdescent : baseEnd_995410 < baseStart_995410 := by decide
  rcases family_descends (prefixWord ++ tailWord_995410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995413 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_995413 : Nat := 118140960795 + 995413 * 2 ^ 59
def prefixEnd_995413 : Nat := 4983230072969 + 3 ^ 40 * 995413 * 2
def baseEnd_995413 : Nat := 511125318734019175759685

theorem tailTrace_995413 : CollatzResearch.WordTrace tailWord_995413 prefixEnd_995413 511125318734019175759685 := by
  unfold tailWord_995413
  simp only [CollatzResearch.WordTrace]
  refine ⟨36305694742796178850878893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24203796495197452567252595 36305694742796178850878893)
  ·
    refine ⟨13614635528548567069079585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36305694742796178850878893 13614635528548567069079585)
    ·
      refine ⟨10210976646411425301809689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13614635528548567069079585 10210976646411425301809689)
      ·
        refine ⟨7658232484808568976357267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10210976646411425301809689 7658232484808568976357267)
        ·
          refine ⟨11487348727212853464535901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658232484808568976357267 11487348727212853464535901)
          ·
            refine ⟨4307755772704820049200963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11487348727212853464535901 4307755772704820049200963)
            ·
              refine ⟨6461633659057230073801445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307755772704820049200963 6461633659057230073801445)
              ·
                refine ⟨1211556311073230638837771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6461633659057230073801445 1211556311073230638837771)
                ·
                  refine ⟨1817334466609845958256657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211556311073230638837771 1817334466609845958256657)
                  ·
                    refine ⟨1363000849957384468692493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1817334466609845958256657 1363000849957384468692493)
                    ·
                      refine ⟨511125318734019175759685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363000849957384468692493 511125318734019175759685)
                      ·
                        rfl

theorem cell23_995413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_995413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995413 prefixEnd_995413 := by exact prefixLift 995413
  have htrace : WordTrace (prefixWord ++ tailWord_995413) baseStart_995413 baseEnd_995413 := by
    simpa [prefixWord, tailWord_995413, baseEnd_995413] using wordTrace_append hprefix tailTrace_995413
  have hstable : (prefixWord ++ tailWord_995413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995413).length < 2 ^ (prefixWord ++ tailWord_995413).sum := by decide
  have hdescent : baseEnd_995413 < baseStart_995413 := by decide
  rcases family_descends (prefixWord ++ tailWord_995413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995416 : List Nat := [2, 1, 2, 2, 1, 4, 4, 7]
def baseStart_995416 : Nat := 118140960795 + 995416 * 2 ^ 59
def prefixEnd_995416 : Nat := 4983230072969 + 3 ^ 40 * 995416 * 2
def baseEnd_995416 : Nat := 18930624413925283852673

theorem tailTrace_995416 : CollatzResearch.WordTrace tailWord_995416 prefixEnd_995416 18930624413925283852673 := by
  unfold tailWord_995416
  simp only [CollatzResearch.WordTrace]
  refine ⟨18152902080892655181619051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24203869441190206908825401 18152902080892655181619051)
  ·
    refine ⟨27229353121338982772428577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18152902080892655181619051 27229353121338982772428577)
    ·
      refine ⟨20422014841004237079321433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27229353121338982772428577 20422014841004237079321433)
      ·
        refine ⟨15316511130753177809491075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20422014841004237079321433 15316511130753177809491075)
        ·
          refine ⟨22974766696129766714236613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15316511130753177809491075 22974766696129766714236613)
          ·
            refine ⟨4307768755524331258919365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22974766696129766714236613 4307768755524331258919365)
            ·
              refine ⟨807706641660812111047381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4307768755524331258919365 807706641660812111047381)
              ·
                refine ⟨18930624413925283852673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 807706641660812111047381 18930624413925283852673)
                ·
                  rfl

theorem cell23_995416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 7].length) (baseStart_995416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995416 prefixEnd_995416 := by exact prefixLift 995416
  have htrace : WordTrace (prefixWord ++ tailWord_995416) baseStart_995416 baseEnd_995416 := by
    simpa [prefixWord, tailWord_995416, baseEnd_995416] using wordTrace_append hprefix tailTrace_995416
  have hstable : (prefixWord ++ tailWord_995416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995416).length < 2 ^ (prefixWord ++ tailWord_995416).sum := by decide
  have hdescent : baseEnd_995416 < baseStart_995416 := by decide
  rcases family_descends (prefixWord ++ tailWord_995416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995427 : List Nat := [1, 1, 1, 5, 1, 1, 5, 3, 1, 2, 2]
def baseStart_995427 : Nat := 118140960795 + 995427 * 2 ^ 59
def prefixEnd_995427 : Nat := 4983230072969 + 3 ^ 40 * 995427 * 2
def baseEnd_995427 : Nat := 511132507463182120984621

theorem tailTrace_995427 : CollatzResearch.WordTrace tailWord_995427 prefixEnd_995427 511132507463182120984621 := by
  unfold tailWord_995427
  simp only [CollatzResearch.WordTrace]
  refine ⟨36306205364745459241888535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24204136909830306161259023 36306205364745459241888535)
  ·
    refine ⟨54459308047118188862832803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36306205364745459241888535 54459308047118188862832803)
    ·
      refine ⟨81688962070677283294249205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54459308047118188862832803 81688962070677283294249205)
      ·
        refine ⟨7658340194125995308835863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81688962070677283294249205 7658340194125995308835863)
        ·
          refine ⟨11487510291188992963253795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658340194125995308835863 11487510291188992963253795)
          ·
            refine ⟨17231265436783489444880693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487510291188992963253795 17231265436783489444880693)
            ·
              refine ⟨1615431134698452135457565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17231265436783489444880693 1615431134698452135457565)
              ·
                refine ⟨605786675511919550796587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1615431134698452135457565 605786675511919550796587)
                ·
                  refine ⟨908680013267879326194881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605786675511919550796587 908680013267879326194881)
                  ·
                    refine ⟨681510009950909494646161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 908680013267879326194881 681510009950909494646161)
                    ·
                      refine ⟨511132507463182120984621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681510009950909494646161 511132507463182120984621)
                      ·
                        rfl

theorem cell23_995427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_995427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995427 prefixEnd_995427 := by exact prefixLift 995427
  have htrace : WordTrace (prefixWord ++ tailWord_995427) baseStart_995427 baseEnd_995427 := by
    simpa [prefixWord, tailWord_995427, baseEnd_995427] using wordTrace_append hprefix tailTrace_995427
  have hstable : (prefixWord ++ tailWord_995427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995427).length < 2 ^ (prefixWord ++ tailWord_995427).sum := by decide
  have hdescent : baseEnd_995427 < baseStart_995427 := by decide
  rcases family_descends (prefixWord ++ tailWord_995427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995460 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_995460 : Nat := 118140960795 + 995460 * 2 ^ 59
def prefixEnd_995460 : Nat := 4983230072969 + 3 ^ 40 * 995460 * 2
def baseEnd_995460 : Nat := 511149452324780491871969

theorem tailTrace_995460 : CollatzResearch.WordTrace tailWord_995460 prefixEnd_995460 511149452324780491871969 := by
  unfold tailWord_995460
  simp only [CollatzResearch.WordTrace]
  refine ⟨18153704486812952938919917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24204939315750603918559889 18153704486812952938919917)
  ·
    refine ⟨6807639182554857352094969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18153704486812952938919917 6807639182554857352094969)
    ·
      refine ⟨5105729386916143014071227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6807639182554857352094969 5105729386916143014071227)
      ·
        refine ⟨7658594080374214521106841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5105729386916143014071227 7658594080374214521106841)
        ·
          refine ⟨5743945560280660890830131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7658594080374214521106841 5743945560280660890830131)
          ·
            refine ⟨8615918340420991336245197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743945560280660890830131 8615918340420991336245197)
            ·
              refine ⟨3230969377657871751091949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8615918340420991336245197 3230969377657871751091949)
              ·
                refine ⟨1211613516621701906659481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3230969377657871751091949 1211613516621701906659481)
                ·
                  refine ⟨908710137466276429994611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1211613516621701906659481 908710137466276429994611)
                  ·
                    refine ⟨1363065206199414644991917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 908710137466276429994611 1363065206199414644991917)
                    ·
                      refine ⟨511149452324780491871969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363065206199414644991917 511149452324780491871969)
                      ·
                        rfl

theorem cell23_995460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_995460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995460 prefixEnd_995460 := by exact prefixLift 995460
  have htrace : WordTrace (prefixWord ++ tailWord_995460) baseStart_995460 baseEnd_995460 := by
    simpa [prefixWord, tailWord_995460, baseEnd_995460] using wordTrace_append hprefix tailTrace_995460
  have hstable : (prefixWord ++ tailWord_995460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995460).length < 2 ^ (prefixWord ++ tailWord_995460).sum := by decide
  have hdescent : baseEnd_995460 < baseStart_995460 := by decide
  rcases family_descends (prefixWord ++ tailWord_995460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995478 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_995478 : Nat := 118140960795 + 995478 * 2 ^ 59
def prefixEnd_995478 : Nat := 4983230072969 + 3 ^ 40 * 995478 * 2
def baseEnd_995478 : Nat := 511158694976561421446887

theorem tailTrace_995478 : CollatzResearch.WordTrace tailWord_995478 prefixEnd_995478 511158694976561421446887 := by
  unfold tailWord_995478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269254092972543434499693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24205376991707129967996725 2269254092972543434499693)
  ·
    refine ⟨850970284864703787937385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2269254092972543434499693 850970284864703787937385)
    ·
      refine ⟨638227713648527840953039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 850970284864703787937385 638227713648527840953039)
      ·
        refine ⟨957341570472791761429559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638227713648527840953039 957341570472791761429559)
        ·
          refine ⟨1436012355709187642144339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957341570472791761429559 1436012355709187642144339)
          ·
            refine ⟨2154018533563781463216509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436012355709187642144339 2154018533563781463216509)
            ·
              refine ⟨807756950086418048706191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2154018533563781463216509 807756950086418048706191)
              ·
                refine ⟨1211635425129627073059287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807756950086418048706191 1211635425129627073059287)
                ·
                  refine ⟨1817453137694440609588931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211635425129627073059287 1817453137694440609588931)
                  ·
                    refine ⟨2726179706541660914383397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1817453137694440609588931 2726179706541660914383397)
                    ·
                      refine ⟨511158694976561421446887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2726179706541660914383397 511158694976561421446887)
                      ·
                        rfl

theorem cell23_995478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_995478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995478 prefixEnd_995478 := by exact prefixLift 995478
  have htrace : WordTrace (prefixWord ++ tailWord_995478) baseStart_995478 baseEnd_995478 := by
    simpa [prefixWord, tailWord_995478, baseEnd_995478] using wordTrace_append hprefix tailTrace_995478
  have hstable : (prefixWord ++ tailWord_995478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995478).length < 2 ^ (prefixWord ++ tailWord_995478).sum := by decide
  have hdescent : baseEnd_995478 < baseStart_995478 := by decide
  rcases family_descends (prefixWord ++ tailWord_995478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995506 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 7]
def baseStart_995506 : Nat := 118140960795 + 995506 * 2 ^ 59
def prefixEnd_995506 : Nat := 4983230072969 + 3 ^ 40 * 995506 * 2
def baseEnd_995506 : Nat := 56797008048320812432973

theorem tailTrace_995506 : CollatzResearch.WordTrace tailWord_995506 prefixEnd_995506 56797008048320812432973 := by
  unfold tailWord_995506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077271682864813933503593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24206057820972837156009581 9077271682864813933503593)
  ·
    refine ⟨6807953762148610450127695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9077271682864813933503593 6807953762148610450127695)
    ·
      refine ⟨10211930643222915675191543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6807953762148610450127695 10211930643222915675191543)
      ·
        refine ⟨15317895964834373512787315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10211930643222915675191543 15317895964834373512787315)
        ·
          refine ⟨22976843947251560269180973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15317895964834373512787315 22976843947251560269180973)
          ·
            refine ⟨8616316480219335100942865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22976843947251560269180973 8616316480219335100942865)
            ·
              refine ⟨6462237360164501325707149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8616316480219335100942865 6462237360164501325707149)
              ·
                refine ⟨2423339010061687997140181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6462237360164501325707149 2423339010061687997140181)
                ·
                  refine ⟨56797008048320812432973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2423339010061687997140181 56797008048320812432973)
                  ·
                    rfl

theorem cell23_995506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_995506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995506 prefixEnd_995506 := by exact prefixLift 995506
  have htrace : WordTrace (prefixWord ++ tailWord_995506) baseStart_995506 baseEnd_995506 := by
    simpa [prefixWord, tailWord_995506, baseEnd_995506] using wordTrace_append hprefix tailTrace_995506
  have hstable : (prefixWord ++ tailWord_995506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995506).length < 2 ^ (prefixWord ++ tailWord_995506).sum := by decide
  have hdescent : baseEnd_995506 < baseStart_995506 := by decide
  rcases family_descends (prefixWord ++ tailWord_995506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995546 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_995546 : Nat := 118140960795 + 995546 * 2 ^ 59
def prefixEnd_995546 : Nat := 4983230072969 + 3 ^ 40 * 995546 * 2
def baseEnd_995546 : Nat := 511193611661067155396573

theorem tailTrace_995546 : CollatzResearch.WordTrace tailWord_995546 prefixEnd_995546 511193611661067155396573 := by
  unfold tailWord_995546
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077636412828585641367623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24207030434209561710313661 9077636412828585641367623)
  ·
    refine ⟨13616454619242878462051435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9077636412828585641367623 13616454619242878462051435)
    ·
      refine ⟨20424681928864317693077153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13616454619242878462051435 20424681928864317693077153)
      ·
        refine ⟨15318511446648238269807865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20424681928864317693077153 15318511446648238269807865)
        ·
          refine ⟨11488883584986178702355899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15318511446648238269807865 11488883584986178702355899)
          ·
            refine ⟨17233325377479268053533849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488883584986178702355899 17233325377479268053533849)
            ·
              refine ⟨12924994033109451040150387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17233325377479268053533849 12924994033109451040150387)
              ·
                refine ⟨19387491049664176560225581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12924994033109451040150387 19387491049664176560225581)
                ·
                  refine ⟨7270309143624066210084593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19387491049664176560225581 7270309143624066210084593)
                  ·
                    refine ⟨5452731857718049657563445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7270309143624066210084593 5452731857718049657563445)
                    ·
                      refine ⟨511193611661067155396573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5452731857718049657563445 511193611661067155396573)
                      ·
                        rfl

theorem cell23_995546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_995546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995546 prefixEnd_995546 := by exact prefixLift 995546
  have htrace : WordTrace (prefixWord ++ tailWord_995546) baseStart_995546 baseEnd_995546 := by
    simpa [prefixWord, tailWord_995546, baseEnd_995546] using wordTrace_append hprefix tailTrace_995546
  have hstable : (prefixWord ++ tailWord_995546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995546).length < 2 ^ (prefixWord ++ tailWord_995546).sum := by decide
  have hdescent : baseEnd_995546 < baseStart_995546 := by decide
  rcases family_descends (prefixWord ++ tailWord_995546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995583 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 3, 4]
def baseStart_995583 : Nat := 118140960795 + 995583 * 2 ^ 59
def prefixEnd_995583 : Nat := 4983230072969 + 3 ^ 40 * 995583 * 2
def baseEnd_995583 : Nat := 170404203481761170211301

theorem tailTrace_995583 : CollatzResearch.WordTrace tailWord_995583 prefixEnd_995583 170404203481761170211301 := by
  unfold tailWord_995583
  simp only [CollatzResearch.WordTrace]
  refine ⟨36311895152180297884567403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24207930101453531923044935 36311895152180297884567403)
  ·
    refine ⟨54467842728270446826851105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36311895152180297884567403 54467842728270446826851105)
    ·
      refine ⟨40850882046202835120138329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54467842728270446826851105 40850882046202835120138329)
      ·
        refine ⟨30638161534652126340103747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40850882046202835120138329 30638161534652126340103747)
        ·
          refine ⟨45957242301978189510155621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30638161534652126340103747 45957242301978189510155621)
          ·
            refine ⟨8616982931620910533154179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45957242301978189510155621 8616982931620910533154179)
            ·
              refine ⟨12925474397431365799731269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8616982931620910533154179 12925474397431365799731269)
              ·
                refine ⟨2423526449518381087449613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12925474397431365799731269 2423526449518381087449613)
                ·
                  refine ⟨908822418569392907793605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2423526449518381087449613 908822418569392907793605)
                  ·
                    refine ⟨170404203481761170211301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 908822418569392907793605 170404203481761170211301)
                    ·
                      rfl

theorem cell23_995583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 4].length) (baseStart_995583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995583 prefixEnd_995583 := by exact prefixLift 995583
  have htrace : WordTrace (prefixWord ++ tailWord_995583) baseStart_995583 baseEnd_995583 := by
    simpa [prefixWord, tailWord_995583, baseEnd_995583] using wordTrace_append hprefix tailTrace_995583
  have hstable : (prefixWord ++ tailWord_995583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995583).length < 2 ^ (prefixWord ++ tailWord_995583).sum := by decide
  have hdescent : baseEnd_995583 < baseStart_995583 := by decide
  rcases family_descends (prefixWord ++ tailWord_995583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995593 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 3]
def baseStart_995593 : Nat := 118140960795 + 995593 * 2 ^ 59
def prefixEnd_995593 : Nat := 4983230072969 + 3 ^ 40 * 995593 * 2
def baseEnd_995593 : Nat := 511217745251828471508857

theorem tailTrace_995593 : CollatzResearch.WordTrace tailWord_995593 prefixEnd_995593 511217745251828471508857 := by
  unfold tailWord_995593
  simp only [CollatzResearch.WordTrace]
  refine ⟨36312259882144069592431433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24208173254762713061620955 36312259882144069592431433)
  ·
    refine ⟨27234194911608052194323575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36312259882144069592431433 27234194911608052194323575)
    ·
      refine ⟨40851292367412078291485363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27234194911608052194323575 40851292367412078291485363)
      ·
        refine ⟨61276938551118117437228045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40851292367412078291485363 61276938551118117437228045)
        ·
          refine ⟨22978851956669294038960517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61276938551118117437228045 22978851956669294038960517)
          ·
            refine ⟨4308534741875492632305097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22978851956669294038960517 4308534741875492632305097)
            ·
              refine ⟨3231401056406619474228823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4308534741875492632305097 3231401056406619474228823)
              ·
                refine ⟨4847101584609929211343235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231401056406619474228823 4847101584609929211343235)
                ·
                  refine ⟨7270652376914893817014853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847101584609929211343235 7270652376914893817014853)
                  ·
                    refine ⟨1363247320671542590690285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7270652376914893817014853 1363247320671542590690285)
                    ·
                      refine ⟨511217745251828471508857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363247320671542590690285 511217745251828471508857)
                      ·
                        rfl

theorem cell23_995593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_995593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995593 prefixEnd_995593 := by exact prefixLift 995593
  have htrace : WordTrace (prefixWord ++ tailWord_995593) baseStart_995593 baseEnd_995593 := by
    simpa [prefixWord, tailWord_995593, baseEnd_995593] using wordTrace_append hprefix tailTrace_995593
  have hstable : (prefixWord ++ tailWord_995593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995593).length < 2 ^ (prefixWord ++ tailWord_995593).sum := by decide
  have hdescent : baseEnd_995593 < baseStart_995593 := by decide
  rcases family_descends (prefixWord ++ tailWord_995593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995596 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 10]
def baseStart_995596 : Nat := 118140960795 + 995596 * 2 ^ 59
def prefixEnd_995596 : Nat := 4983230072969 + 3 ^ 40 * 995596 * 2
def baseEnd_995596 : Nat := 56802142854865773307927

theorem tailTrace_995596 : CollatzResearch.WordTrace tailWord_995596 prefixEnd_995596 56802142854865773307927 := by
  unfold tailWord_995596
  simp only [CollatzResearch.WordTrace]
  refine ⟨18156184650566600552395321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24208246200755467403193761 18156184650566600552395321)
  ·
    refine ⟨13617138487924950414296491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18156184650566600552395321 13617138487924950414296491)
    ·
      refine ⟨20425707731887425621444737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13617138487924950414296491 20425707731887425621444737)
      ·
        refine ⟨15319280798915569216083553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20425707731887425621444737 15319280798915569216083553)
        ·
          refine ⟨11489460599186676912062665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15319280798915569216083553 11489460599186676912062665)
          ·
            refine ⟨8617095449390007684046999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11489460599186676912062665 8617095449390007684046999)
            ·
              refine ⟨12925643174085011526070499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617095449390007684046999 12925643174085011526070499)
              ·
                refine ⟨19388464761127517289105749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12925643174085011526070499 19388464761127517289105749)
                ·
                  refine ⟨56802142854865773307927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 19388464761127517289105749 56802142854865773307927)
                  ·
                    rfl

theorem cell23_995596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_995596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995596 prefixEnd_995596 := by exact prefixLift 995596
  have htrace : WordTrace (prefixWord ++ tailWord_995596) baseStart_995596 baseEnd_995596 := by
    simpa [prefixWord, tailWord_995596, baseEnd_995596] using wordTrace_append hprefix tailTrace_995596
  have hstable : (prefixWord ++ tailWord_995596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995596).length < 2 ^ (prefixWord ++ tailWord_995596).sum := by decide
  have hdescent : baseEnd_995596 < baseStart_995596 := by decide
  rcases family_descends (prefixWord ++ tailWord_995596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995640 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 3, 1, 3]
def baseStart_995640 : Nat := 118140960795 + 995640 * 2 ^ 59
def prefixEnd_995640 : Nat := 4983230072969 + 3 ^ 40 * 995640 * 2
def baseEnd_995640 : Nat := 511241878842589787621141

theorem tailTrace_995640 : CollatzResearch.WordTrace tailWord_995640 prefixEnd_995640 511241878842589787621141 := by
  unfold tailWord_995640
  simp only [CollatzResearch.WordTrace]
  refine ⟨18156987056486898309696187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24209316075315864412928249 18156987056486898309696187)
  ·
    refine ⟨27235480584730347464544281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18156987056486898309696187 27235480584730347464544281)
    ·
      refine ⟨20426610438547760598408211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27235480584730347464544281 20426610438547760598408211)
      ·
        refine ⟨30639915657821640897612317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20426610438547760598408211 30639915657821640897612317)
        ·
          refine ⟨11489968371683115336604619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30639915657821640897612317 11489968371683115336604619)
          ·
            refine ⟨17234952557524673004906929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11489968371683115336604619 17234952557524673004906929)
            ·
              refine ⟨12926214418143504753680197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17234952557524673004906929 12926214418143504753680197)
              ·
                refine ⟨2423665203401907141315037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12926214418143504753680197 2423665203401907141315037)
                ·
                  refine ⟨908874451275715177993139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2423665203401907141315037 908874451275715177993139)
                  ·
                    refine ⟨1363311676913572766989709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 908874451275715177993139 1363311676913572766989709)
                    ·
                      refine ⟨511241878842589787621141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363311676913572766989709 511241878842589787621141)
                      ·
                        rfl

theorem cell23_995640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_995640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995640 prefixEnd_995640 := by exact prefixLift 995640
  have htrace : WordTrace (prefixWord ++ tailWord_995640) baseStart_995640 baseEnd_995640 := by
    simpa [prefixWord, tailWord_995640, baseEnd_995640] using wordTrace_append hprefix tailTrace_995640
  have hstable : (prefixWord ++ tailWord_995640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995640).length < 2 ^ (prefixWord ++ tailWord_995640).sum := by decide
  have hdescent : baseEnd_995640 < baseStart_995640 := by decide
  rcases family_descends (prefixWord ++ tailWord_995640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995657 : List Nat := [1, 2, 1, 1, 2, 3, 1, 7, 1, 1, 3]
def baseStart_995657 : Nat := 118140960795 + 995657 * 2 ^ 59
def prefixEnd_995657 : Nat := 4983230072969 + 3 ^ 40 * 995657 * 2
def baseEnd_995657 : Nat := 511250608013716221108563

theorem tailTrace_995657 : CollatzResearch.WordTrace tailWord_995657 prefixEnd_995657 511250608013716221108563 := by
  unfold tailWord_995657
  simp only [CollatzResearch.WordTrace]
  refine ⟨36314594153912208522761225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24209729435941472348507483 36314594153912208522761225)
  ·
    refine ⟨27235945615434156392070919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36314594153912208522761225 27235945615434156392070919)
    ·
      refine ⟨40853918423151234588106379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27235945615434156392070919 40853918423151234588106379)
      ·
        refine ⟨61280877634726851882159569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40853918423151234588106379 61280877634726851882159569)
        ·
          refine ⟨45960658226045138911619677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61280877634726851882159569 45960658226045138911619677)
          ·
            refine ⟨17235246834766927091857379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45960658226045138911619677 17235246834766927091857379)
            ·
              refine ⟨25852870252150390637786069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17235246834766927091857379 25852870252150390637786069)
              ·
                refine ⟨605926646534774780573111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25852870252150390637786069 605926646534774780573111)
                ·
                  refine ⟨908889969802162170859667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605926646534774780573111 908889969802162170859667)
                  ·
                    refine ⟨1363334954703243256289501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 908889969802162170859667 1363334954703243256289501)
                    ·
                      refine ⟨511250608013716221108563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363334954703243256289501 511250608013716221108563)
                      ·
                        rfl

theorem cell23_995657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 1, 3].length) (baseStart_995657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995657 prefixEnd_995657 := by exact prefixLift 995657
  have htrace : WordTrace (prefixWord ++ tailWord_995657) baseStart_995657 baseEnd_995657 := by
    simpa [prefixWord, tailWord_995657, baseEnd_995657] using wordTrace_append hprefix tailTrace_995657
  have hstable : (prefixWord ++ tailWord_995657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995657).length < 2 ^ (prefixWord ++ tailWord_995657).sum := by decide
  have hdescent : baseEnd_995657 < baseStart_995657 := by decide
  rcases family_descends (prefixWord ++ tailWord_995657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995683 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 5]
def baseStart_995683 : Nat := 118140960795 + 995683 * 2 ^ 59
def prefixEnd_995683 : Nat := 4983230072969 + 3 ^ 40 * 995683 * 2
def baseEnd_995683 : Nat := 511263958510733119383443

theorem tailTrace_995683 : CollatzResearch.WordTrace tailWord_995683 prefixEnd_995683 511263958510733119383443 := by
  unfold tailWord_995683
  simp only [CollatzResearch.WordTrace]
  refine ⟨36315542451818014963207703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24210361634545343308805135 36315542451818014963207703)
  ·
    refine ⟨54473313677727022444811555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36315542451818014963207703 54473313677727022444811555)
    ·
      refine ⟨81709970516590533667217333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54473313677727022444811555 81709970516590533667217333)
      ·
        refine ⟨7660309735930362531301625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81709970516590533667217333 7660309735930362531301625)
        ·
          refine ⟨5745232301947771898476219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7660309735930362531301625 5745232301947771898476219)
          ·
            refine ⟨8617848452921657847714329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745232301947771898476219 8617848452921657847714329)
            ·
              refine ⟨6463386339691243385785747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8617848452921657847714329 6463386339691243385785747)
              ·
                refine ⟨9695079509536865078678621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6463386339691243385785747 9695079509536865078678621)
                ·
                  refine ⟨3635654816076324404504483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9695079509536865078678621 3635654816076324404504483)
                  ·
                    refine ⟨5453482224114486606756725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3635654816076324404504483 5453482224114486606756725)
                    ·
                      refine ⟨511263958510733119383443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5453482224114486606756725 511263958510733119383443)
                      ·
                        rfl

theorem cell23_995683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_995683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995683 prefixEnd_995683 := by exact prefixLift 995683
  have htrace : WordTrace (prefixWord ++ tailWord_995683) baseStart_995683 baseEnd_995683 := by
    simpa [prefixWord, tailWord_995683, baseEnd_995683] using wordTrace_append hprefix tailTrace_995683
  have hstable : (prefixWord ++ tailWord_995683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995683).length < 2 ^ (prefixWord ++ tailWord_995683).sum := by decide
  have hdescent : baseEnd_995683 < baseStart_995683 := by decide
  rcases family_descends (prefixWord ++ tailWord_995683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995690 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_995690 : Nat := 118140960795 + 995690 * 2 ^ 59
def prefixEnd_995690 : Nat := 4983230072969 + 3 ^ 40 * 995690 * 2
def baseEnd_995690 : Nat := 170422517625104863998637

theorem tailTrace_995690 : CollatzResearch.WordTrace tailWord_995690 prefixEnd_995690 170422517625104863998637 := by
  unfold tailWord_995690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9078949440698163789678131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24210531841861770105808349 9078949440698163789678131)
  ·
    refine ⟨13618424161047245684517197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9078949440698163789678131 13618424161047245684517197)
    ·
      refine ⟨5106909060392717131693949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13618424161047245684517197 5106909060392717131693949)
      ·
        refine ⟨1915090897647268924385231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5106909060392717131693949 1915090897647268924385231)
        ·
          refine ⟨2872636346470903386577847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915090897647268924385231 2872636346470903386577847)
          ·
            refine ⟨4308954519706355079866771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2872636346470903386577847 4308954519706355079866771)
            ·
              refine ⟨6463431779559532619800157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308954519706355079866771 6463431779559532619800157)
              ·
                refine ⟨2423786917334824732425059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6463431779559532619800157 2423786917334824732425059)
                ·
                  refine ⟨3635680376002237098637589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423786917334824732425059 3635680376002237098637589)
                  ·
                    refine ⟨170422517625104863998637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3635680376002237098637589 170422517625104863998637)
                    ·
                      rfl

theorem cell23_995690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_995690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995690 prefixEnd_995690 := by exact prefixLift 995690
  have htrace : WordTrace (prefixWord ++ tailWord_995690) baseStart_995690 baseEnd_995690 := by
    simpa [prefixWord, tailWord_995690, baseEnd_995690] using wordTrace_append hprefix tailTrace_995690
  have hstable : (prefixWord ++ tailWord_995690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995690).length < 2 ^ (prefixWord ++ tailWord_995690).sum := by decide
  have hdescent : baseEnd_995690 < baseStart_995690 := by decide
  rcases family_descends (prefixWord ++ tailWord_995690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995747 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 3]
def baseStart_995747 : Nat := 118140960795 + 995747 * 2 ^ 59
def prefixEnd_995747 : Nat := 4983230072969 + 3 ^ 40 * 995747 * 2
def baseEnd_995747 : Nat := 511296821272620868983149

theorem tailTrace_995747 : CollatzResearch.WordTrace tailWord_995747 prefixEnd_995747 511296821272620868983149 := by
  unfold tailWord_995747
  simp only [CollatzResearch.WordTrace]
  refine ⟨36317876723586153893537495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24211917815724102595691663 36317876723586153893537495)
  ·
    refine ⟨54476815085379230840306243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36317876723586153893537495 54476815085379230840306243)
    ·
      refine ⟨81715222628068846260459365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54476815085379230840306243 81715222628068846260459365)
      ·
        refine ⟨15321604242762908673836131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81715222628068846260459365 15321604242762908673836131)
        ·
          refine ⟨22982406364144363010754197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15321604242762908673836131 22982406364144363010754197)
          ·
            refine ⟨1077300298319267016129103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22982406364144363010754197 1077300298319267016129103)
            ·
              refine ⟨1615950447478900524193655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077300298319267016129103 1615950447478900524193655)
              ·
                refine ⟨2423925671218350786290483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615950447478900524193655 2423925671218350786290483)
                ·
                  refine ⟨3635888506827526179435725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423925671218350786290483 3635888506827526179435725)
                  ·
                    refine ⟨1363458190060322317288397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3635888506827526179435725 1363458190060322317288397)
                    ·
                      refine ⟨511296821272620868983149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363458190060322317288397 511296821272620868983149)
                      ·
                        rfl

theorem cell23_995747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_995747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995747 prefixEnd_995747 := by exact prefixLift 995747
  have htrace : WordTrace (prefixWord ++ tailWord_995747) baseStart_995747 baseEnd_995747 := by
    simpa [prefixWord, tailWord_995747, baseEnd_995747] using wordTrace_append hprefix tailTrace_995747
  have hstable : (prefixWord ++ tailWord_995747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995747).length < 2 ^ (prefixWord ++ tailWord_995747).sum := by decide
  have hdescent : baseEnd_995747 < baseStart_995747 := by decide
  rcases family_descends (prefixWord ++ tailWord_995747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995753 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_995753 : Nat := 118140960795 + 995753 * 2 ^ 59
def prefixEnd_995753 : Nat := 4983230072969 + 3 ^ 40 * 995753 * 2
def baseEnd_995753 : Nat := 511299902156547845508121

theorem tailTrace_995753 : CollatzResearch.WordTrace tailWord_995753 prefixEnd_995753 511299902156547845508121 := by
  unfold tailWord_995753
  simp only [CollatzResearch.WordTrace]
  refine ⟨36318095561564416918255913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24212063707709611278837275 36318095561564416918255913)
  ·
    refine ⟨27238571671173312688691935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36318095561564416918255913 27238571671173312688691935)
    ·
      refine ⟨40857857506759969033037903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27238571671173312688691935 40857857506759969033037903)
      ·
        refine ⟨61286786260139953549556855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40857857506759969033037903 61286786260139953549556855)
        ·
          refine ⟨91930179390209930324335283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61286786260139953549556855 91930179390209930324335283)
          ·
            refine ⟨137895269085314895486502925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91930179390209930324335283 137895269085314895486502925)
            ·
              refine ⟨51710725906993085807438597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137895269085314895486502925 51710725906993085807438597)
              ·
                refine ⟨9695761107561203588894737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51710725906993085807438597 9695761107561203588894737)
                ·
                  refine ⟨7271820830670902691671053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9695761107561203588894737 7271820830670902691671053)
                  ·
                    refine ⟨2726932811501588509376645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7271820830670902691671053 2726932811501588509376645)
                    ·
                      refine ⟨511299902156547845508121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2726932811501588509376645 511299902156547845508121)
                      ·
                        rfl

theorem cell23_995753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_995753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995753 prefixEnd_995753 := by exact prefixLift 995753
  have htrace : WordTrace (prefixWord ++ tailWord_995753) baseStart_995753 baseEnd_995753 := by
    simpa [prefixWord, tailWord_995753, baseEnd_995753] using wordTrace_append hprefix tailTrace_995753
  have hstable : (prefixWord ++ tailWord_995753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995753).length < 2 ^ (prefixWord ++ tailWord_995753).sum := by decide
  have hdescent : baseEnd_995753 < baseStart_995753 := by decide
  rcases family_descends (prefixWord ++ tailWord_995753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995754 : List Nat := [3, 1, 6, 1, 1, 1, 1, 9]
def baseStart_995754 : Nat := 118140960795 + 995754 * 2 ^ 59
def prefixEnd_995754 : Nat := 4983230072969 + 3 ^ 40 * 995754 * 2
def baseEnd_995754 : Nat := 18937052431007494133171

theorem tailTrace_995754 : CollatzResearch.WordTrace tailWord_995754 prefixEnd_995754 18937052431007494133171 := by
  unfold tailWord_995754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079533008640198522260579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24212088023040529392694877 9079533008640198522260579)
  ·
    refine ⟨13619299512960297783390869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9079533008640198522260579 13619299512960297783390869)
    ·
      refine ⟨638404664670013958596447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13619299512960297783390869 638404664670013958596447)
      ·
        refine ⟨957606997005020937894671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638404664670013958596447 957606997005020937894671)
        ·
          refine ⟨1436410495507531406842007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957606997005020937894671 1436410495507531406842007)
          ·
            refine ⟨2154615743261297110263011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436410495507531406842007 2154615743261297110263011)
            ·
              refine ⟨3231923614891945665394517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154615743261297110263011 3231923614891945665394517)
              ·
                refine ⟨18937052431007494133171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3231923614891945665394517 18937052431007494133171)
                ·
                  rfl

theorem cell23_995754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 9].length) (baseStart_995754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995754 prefixEnd_995754 := by exact prefixLift 995754
  have htrace : WordTrace (prefixWord ++ tailWord_995754) baseStart_995754 baseEnd_995754 := by
    simpa [prefixWord, tailWord_995754, baseEnd_995754] using wordTrace_append hprefix tailTrace_995754
  have hstable : (prefixWord ++ tailWord_995754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995754).length < 2 ^ (prefixWord ++ tailWord_995754).sum := by decide
  have hdescent : baseEnd_995754 < baseStart_995754 := by decide
  rcases family_descends (prefixWord ++ tailWord_995754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995765 : List Nat := [1, 3, 3, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_995765 : Nat := 118140960795 + 995765 * 2 ^ 59
def prefixEnd_995765 : Nat := 4983230072969 + 3 ^ 40 * 995765 * 2
def baseEnd_995765 : Nat := 511306063924401798558067

theorem tailTrace_995765 : CollatzResearch.WordTrace tailWord_995765 prefixEnd_995765 511306063924401798558067 := by
  unfold tailWord_995765
  simp only [CollatzResearch.WordTrace]
  refine ⟨36318533237520942967692749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24212355491680628645128499 36318533237520942967692749)
  ·
    refine ⟨13619449964070353612884781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36318533237520942967692749 13619449964070353612884781)
    ·
      refine ⟨5107293736526382604831793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13619449964070353612884781 5107293736526382604831793)
      ·
        refine ⟨3830470302394786953623845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5107293736526382604831793 3830470302394786953623845)
        ·
          refine ⟨718213181699022553804471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3830470302394786953623845 718213181699022553804471)
          ·
            refine ⟨1077319772548533830706707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718213181699022553804471 1077319772548533830706707)
            ·
              refine ⟨1615979658822800746060061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077319772548533830706707 1615979658822800746060061)
              ·
                refine ⟨605992372058550279772523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1615979658822800746060061 605992372058550279772523)
                ·
                  refine ⟨908988558087825419658785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605992372058550279772523 908988558087825419658785)
                  ·
                    refine ⟨681741418565869064744089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 908988558087825419658785 681741418565869064744089)
                    ·
                      refine ⟨511306063924401798558067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681741418565869064744089 511306063924401798558067)
                      ·
                        rfl

theorem cell23_995765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_995765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995765 prefixEnd_995765 := by exact prefixLift 995765
  have htrace : WordTrace (prefixWord ++ tailWord_995765) baseStart_995765 baseEnd_995765 := by
    simpa [prefixWord, tailWord_995765, baseEnd_995765] using wordTrace_append hprefix tailTrace_995765
  have hstable : (prefixWord ++ tailWord_995765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995765).length < 2 ^ (prefixWord ++ tailWord_995765).sum := by decide
  have hdescent : baseEnd_995765 < baseStart_995765 := by decide
  rcases family_descends (prefixWord ++ tailWord_995765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995774 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_995774 : Nat := 118140960795 + 995774 * 2 ^ 59
def prefixEnd_995774 : Nat := 4983230072969 + 3 ^ 40 * 995774 * 2
def baseEnd_995774 : Nat := 511310685250292263345525

theorem tailTrace_995774 : CollatzResearch.WordTrace tailWord_995774 prefixEnd_995774 511310685250292263345525 := by
  unfold tailWord_995774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539857686811042188096297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24212574329658891669846917 4539857686811042188096297)
  ·
    refine ⟨3404893265108281641072223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4539857686811042188096297 3404893265108281641072223)
    ·
      refine ⟨5107339897662422461608335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404893265108281641072223 5107339897662422461608335)
      ·
        refine ⟨7661009846493633692412503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5107339897662422461608335 7661009846493633692412503)
        ·
          refine ⟨11491514769740450538618755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661009846493633692412503 11491514769740450538618755)
          ·
            refine ⟨17237272154610675807928133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11491514769740450538618755 17237272154610675807928133)
            ·
              refine ⟨3231988528989501713986525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17237272154610675807928133 3231988528989501713986525)
              ·
                refine ⟨1211995698371063142744947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3231988528989501713986525 1211995698371063142744947)
                ·
                  refine ⟨1817993547556594714117421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211995698371063142744947 1817993547556594714117421)
                  ·
                    refine ⟨681747580333723017794033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1817993547556594714117421 681747580333723017794033)
                    ·
                      refine ⟨511310685250292263345525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681747580333723017794033 511310685250292263345525)
                      ·
                        rfl

theorem cell23_995774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_995774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995774 prefixEnd_995774 := by exact prefixLift 995774
  have htrace : WordTrace (prefixWord ++ tailWord_995774) baseStart_995774 baseEnd_995774 := by
    simpa [prefixWord, tailWord_995774, baseEnd_995774] using wordTrace_append hprefix tailTrace_995774
  have hstable : (prefixWord ++ tailWord_995774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995774).length < 2 ^ (prefixWord ++ tailWord_995774).sum := by decide
  have hdescent : baseEnd_995774 < baseStart_995774 := by decide
  rcases family_descends (prefixWord ++ tailWord_995774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995790 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_995790 : Nat := 118140960795 + 995790 * 2 ^ 59
def prefixEnd_995790 : Nat := 4983230072969 + 3 ^ 40 * 995790 * 2
def baseEnd_995790 : Nat := 511318900940764200745451

theorem tailTrace_995790 : CollatzResearch.WordTrace tailWord_995790 prefixEnd_995790 511318900940764200745451 := by
  unfold tailWord_995790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539930632803796529669103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24212963374953581491568549 4539930632803796529669103)
  ·
    refine ⟨6809895949205694794503655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4539930632803796529669103 6809895949205694794503655)
    ·
      refine ⟨10214843923808542191755483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809895949205694794503655 10214843923808542191755483)
      ·
        refine ⟨15322265885712813287633225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10214843923808542191755483 15322265885712813287633225)
        ·
          refine ⟨11491699414284609965724919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15322265885712813287633225 11491699414284609965724919)
          ·
            refine ⟨17237549121426914948587379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11491699414284609965724919 17237549121426914948587379)
            ·
              refine ⟨25856323682140372422881069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17237549121426914948587379 25856323682140372422881069)
              ·
                refine ⟨9696121380802639658580401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25856323682140372422881069 9696121380802639658580401)
                ·
                  refine ⟨7272091035601979743935301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9696121380802639658580401 7272091035601979743935301)
                  ·
                    refine ⟨1363517069175371201987869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7272091035601979743935301 1363517069175371201987869)
                    ·
                      refine ⟨511318900940764200745451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363517069175371201987869 511318900940764200745451)
                      ·
                        rfl

theorem cell23_995790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_995790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995790 prefixEnd_995790 := by exact prefixLift 995790
  have htrace : WordTrace (prefixWord ++ tailWord_995790) baseStart_995790 baseEnd_995790 := by
    simpa [prefixWord, tailWord_995790, baseEnd_995790] using wordTrace_append hprefix tailTrace_995790
  have hstable : (prefixWord ++ tailWord_995790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995790).length < 2 ^ (prefixWord ++ tailWord_995790).sum := by decide
  have hdescent : baseEnd_995790 < baseStart_995790 := by decide
  rcases family_descends (prefixWord ++ tailWord_995790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995844 : List Nat := [2, 3, 2, 3, 1, 2, 1, 4, 5]
def baseStart_995844 : Nat := 118140960795 + 995844 * 2 ^ 59
def prefixEnd_995844 : Nat := 4983230072969 + 3 ^ 40 * 995844 * 2
def baseEnd_995844 : Nat := 56816292099567443274467

theorem tailTrace_995844 : CollatzResearch.WordTrace tailWord_995844 prefixEnd_995844 56816292099567443274467 := by
  unfold tailWord_995844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18160707302117369729909293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24214276402823159639879057 18160707302117369729909293)
  ·
    refine ⟨6810265238294013648715985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18160707302117369729909293 6810265238294013648715985)
    ·
      refine ⟨5107698928720510236536989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6810265238294013648715985 5107698928720510236536989)
      ·
        refine ⟨1915387098270191338701371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5107698928720510236536989 1915387098270191338701371)
        ·
          refine ⟨2873080647405287008052057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915387098270191338701371 2873080647405287008052057)
          ·
            refine ⟨2154810485553965256039043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2873080647405287008052057 2154810485553965256039043)
            ·
              refine ⟨3232215728330947884058565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154810485553965256039043 3232215728330947884058565)
              ·
                refine ⟨606040449062052728260981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3232215728330947884058565 606040449062052728260981)
                ·
                  refine ⟨56816292099567443274467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 606040449062052728260981 56816292099567443274467)
                  ·
                    rfl

theorem cell23_995844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_995844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995844 prefixEnd_995844 := by exact prefixLift 995844
  have htrace : WordTrace (prefixWord ++ tailWord_995844) baseStart_995844 baseEnd_995844 := by
    simpa [prefixWord, tailWord_995844, baseEnd_995844] using wordTrace_append hprefix tailTrace_995844
  have hstable : (prefixWord ++ tailWord_995844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995844).length < 2 ^ (prefixWord ++ tailWord_995844).sum := by decide
  have hdescent : baseEnd_995844 < baseStart_995844 := by decide
  rcases family_descends (prefixWord ++ tailWord_995844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995850 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_995850 : Nat := 118140960795 + 995850 * 2 ^ 59
def prefixEnd_995850 : Nat := 4983230072969 + 3 ^ 40 * 995850 * 2
def baseEnd_995850 : Nat := 511349709780033965995175

theorem tailTrace_995850 : CollatzResearch.WordTrace tailWord_995850 prefixEnd_995850 511349709780033965995175 := by
  unfold tailWord_995850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080408360553250621134251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24214422294808668323024669 9080408360553250621134251)
  ·
    refine ⟨13620612540829875931701377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9080408360553250621134251 13620612540829875931701377)
    ·
      refine ⟨10215459405622406948776033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13620612540829875931701377 10215459405622406948776033)
      ·
        refine ⟨7661594554216805211582025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10215459405622406948776033 7661594554216805211582025)
        ·
          refine ⟨5746195915662603908686519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7661594554216805211582025 5746195915662603908686519)
          ·
            refine ⟨8619293873493905863029779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746195915662603908686519 8619293873493905863029779)
            ·
              refine ⟨12928940810240858794544669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8619293873493905863029779 12928940810240858794544669)
              ·
                refine ⟨4848352803840322047954251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12928940810240858794544669 4848352803840322047954251)
                ·
                  refine ⟨7272529205760483071931377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4848352803840322047954251 7272529205760483071931377)
                  ·
                    refine ⟨5454396904320362303948533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7272529205760483071931377 5454396904320362303948533)
                    ·
                      refine ⟨511349709780033965995175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5454396904320362303948533 511349709780033965995175)
                      ·
                        rfl

theorem cell23_995850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_995850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995850 prefixEnd_995850 := by exact prefixLift 995850
  have htrace : WordTrace (prefixWord ++ tailWord_995850) baseStart_995850 baseEnd_995850 := by
    simpa [prefixWord, tailWord_995850, baseEnd_995850] using wordTrace_append hprefix tailTrace_995850
  have hstable : (prefixWord ++ tailWord_995850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995850).length < 2 ^ (prefixWord ++ tailWord_995850).sum := by decide
  have hdescent : baseEnd_995850 < baseStart_995850 := by decide
  rcases family_descends (prefixWord ++ tailWord_995850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995877 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_995877 : Nat := 118140960795 + 995877 * 2 ^ 59
def prefixEnd_995877 : Nat := 4983230072969 + 3 ^ 40 * 995877 * 2
def baseEnd_995877 : Nat := 511363573757705360357551

theorem tailTrace_995877 : CollatzResearch.WordTrace tailWord_995877 prefixEnd_995877 511363573757705360357551 := by
  unfold tailWord_995877
  simp only [CollatzResearch.WordTrace]
  refine ⟨36322618213115186095769885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24215078808743457397179923 36322618213115186095769885)
  ·
    refine ⟨13620981829918194785913707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36322618213115186095769885 13620981829918194785913707)
    ·
      refine ⟨20431472744877292178870561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13620981829918194785913707 20431472744877292178870561)
      ·
        refine ⟨15323604558657969134152921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20431472744877292178870561 15323604558657969134152921)
        ·
          refine ⟨11492703418993476850614691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15323604558657969134152921 11492703418993476850614691)
          ·
            refine ⟨17239055128490215275922037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492703418993476850614691 17239055128490215275922037)
            ·
              refine ⟨1616161418295957682117691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17239055128490215275922037 1616161418295957682117691)
              ·
                refine ⟨2424242127443936523176537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616161418295957682117691 2424242127443936523176537)
                ·
                  refine ⟨1818181595582952392382403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2424242127443936523176537 1818181595582952392382403)
                  ·
                    refine ⟨2727272393374428588573605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1818181595582952392382403 2727272393374428588573605)
                    ·
                      refine ⟨511363573757705360357551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2727272393374428588573605 511363573757705360357551)
                      ·
                        rfl

theorem cell23_995877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_995877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995877 prefixEnd_995877 := by exact prefixLift 995877
  have htrace : WordTrace (prefixWord ++ tailWord_995877) baseStart_995877 baseEnd_995877 := by
    simpa [prefixWord, tailWord_995877, baseEnd_995877] using wordTrace_append hprefix tailTrace_995877
  have hstable : (prefixWord ++ tailWord_995877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995877).length < 2 ^ (prefixWord ++ tailWord_995877).sum := by decide
  have hdescent : baseEnd_995877 < baseStart_995877 := by decide
  rcases family_descends (prefixWord ++ tailWord_995877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995890 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_995890 : Nat := 118140960795 + 995890 * 2 ^ 59
def prefixEnd_995890 : Nat := 4983230072969 + 3 ^ 40 * 995890 * 2
def baseEnd_995890 : Nat := 511370249006213809494991

theorem tailTrace_995890 : CollatzResearch.WordTrace tailWord_995890 prefixEnd_995890 511370249006213809494991 := by
  unfold tailWord_995890
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080773090517022328998281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24215394908045392877328749 9080773090517022328998281)
  ·
    refine ⟨6810579817887766746748711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9080773090517022328998281 6810579817887766746748711)
    ·
      refine ⟨10215869726831650120123067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6810579817887766746748711 10215869726831650120123067)
      ·
        refine ⟨15323804590247475180184601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10215869726831650120123067 15323804590247475180184601)
        ·
          refine ⟨11492853442685606385138451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15323804590247475180184601 11492853442685606385138451)
          ·
            refine ⟨17239280164028409577707677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492853442685606385138451 17239280164028409577707677)
            ·
              refine ⟨6464730061510653591640379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17239280164028409577707677 6464730061510653591640379)
              ·
                refine ⟨9697095092265980387460569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464730061510653591640379 9697095092265980387460569)
                ·
                  refine ⟨7272821319199485290595427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9697095092265980387460569 7272821319199485290595427)
                  ·
                    refine ⟨10909231978799227935893141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7272821319199485290595427 10909231978799227935893141)
                    ·
                      refine ⟨511370249006213809494991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10909231978799227935893141 511370249006213809494991)
                      ·
                        rfl

theorem cell23_995890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_995890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995890 prefixEnd_995890 := by exact prefixLift 995890
  have htrace : WordTrace (prefixWord ++ tailWord_995890) baseStart_995890 baseEnd_995890 := by
    simpa [prefixWord, tailWord_995890, baseEnd_995890] using wordTrace_append hprefix tailTrace_995890
  have hstable : (prefixWord ++ tailWord_995890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995890).length < 2 ^ (prefixWord ++ tailWord_995890).sum := by decide
  have hdescent : baseEnd_995890 < baseStart_995890 := by decide
  rcases family_descends (prefixWord ++ tailWord_995890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995897 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 3]
def baseStart_995897 : Nat := 118140960795 + 995897 * 2 ^ 59
def prefixEnd_995897 : Nat := 4983230072969 + 3 ^ 40 * 995897 * 2
def baseEnd_995897 : Nat := 511373843370795282107459

theorem tailTrace_995897 : CollatzResearch.WordTrace tailWord_995897 prefixEnd_995897 511373843370795282107459 := by
  unfold tailWord_995897
  simp only [CollatzResearch.WordTrace]
  refine ⟨36323347673042729511497945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24215565115361819674331963 36323347673042729511497945)
  ·
    refine ⟨27242510754782047133623459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36323347673042729511497945 27242510754782047133623459)
    ·
      refine ⟨40863766132173070700435189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27242510754782047133623459 40863766132173070700435189)
      ·
        refine ⟨3830978074891225378165799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40863766132173070700435189 3830978074891225378165799)
        ·
          refine ⟨5746467112336838067248699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830978074891225378165799 5746467112336838067248699)
          ·
            refine ⟨8619700668505257100873049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746467112336838067248699 8619700668505257100873049)
            ·
              refine ⟨6464775501378942825654787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8619700668505257100873049 6464775501378942825654787)
              ·
                refine ⟨9697163252068414238482181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464775501378942825654787 9697163252068414238482181)
                ·
                  refine ⟨1818218109762827669715409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9697163252068414238482181 1818218109762827669715409)
                  ·
                    refine ⟨1363663582322120752286557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1818218109762827669715409 1363663582322120752286557)
                    ·
                      refine ⟨511373843370795282107459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363663582322120752286557 511373843370795282107459)
                      ·
                        rfl

theorem cell23_995897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_995897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995897 prefixEnd_995897 := by exact prefixLift 995897
  have htrace : WordTrace (prefixWord ++ tailWord_995897) baseStart_995897 baseEnd_995897 := by
    simpa [prefixWord, tailWord_995897, baseEnd_995897] using wordTrace_append hprefix tailTrace_995897
  have hstable : (prefixWord ++ tailWord_995897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995897).length < 2 ^ (prefixWord ++ tailWord_995897).sum := by decide
  have hdescent : baseEnd_995897 < baseStart_995897 := by decide
  rcases family_descends (prefixWord ++ tailWord_995897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995904 : List Nat := [2, 1, 1, 2, 2, 2, 4, 4, 1, 4]
def baseStart_995904 : Nat := 118140960795 + 995904 * 2 ^ 59
def prefixEnd_995904 : Nat := 4983230072969 + 3 ^ 40 * 995904 * 2
def baseEnd_995904 : Nat := 170459145911792251573309

theorem tailTrace_995904 : CollatzResearch.WordTrace tailWord_995904 prefixEnd_995904 170459145911792251573309 := by
  unfold tailWord_995904
  simp only [CollatzResearch.WordTrace]
  refine ⟨18161801492008684853501383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24215735322678246471335177 18161801492008684853501383)
  ·
    refine ⟨27242702238013027280252075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18161801492008684853501383 27242702238013027280252075)
    ·
      refine ⟨40864053357019540920378113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27242702238013027280252075 40864053357019540920378113)
      ·
        refine ⟨30648040017764655690283585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40864053357019540920378113 30648040017764655690283585)
        ·
          refine ⟨22986030013323491767712689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30648040017764655690283585 22986030013323491767712689)
          ·
            refine ⟨17239522509992618825784517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22986030013323491767712689 17239522509992618825784517)
            ·
              refine ⟨3232410470623616029834597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17239522509992618825784517 3232410470623616029834597)
              ·
                refine ⟨606076963241928005593987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3232410470623616029834597 606076963241928005593987)
                ·
                  refine ⟨909115444862892008390981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606076963241928005593987 909115444862892008390981)
                  ·
                    refine ⟨170459145911792251573309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 909115444862892008390981 170459145911792251573309)
                    ·
                      rfl

theorem cell23_995904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 4].length) (baseStart_995904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995904 prefixEnd_995904 := by exact prefixLift 995904
  have htrace : WordTrace (prefixWord ++ tailWord_995904) baseStart_995904 baseEnd_995904 := by
    simpa [prefixWord, tailWord_995904, baseEnd_995904] using wordTrace_append hprefix tailTrace_995904
  have hstable : (prefixWord ++ tailWord_995904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995904).length < 2 ^ (prefixWord ++ tailWord_995904).sum := by decide
  have hdescent : baseEnd_995904 < baseStart_995904 := by decide
  rcases family_descends (prefixWord ++ tailWord_995904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995960 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 3, 6]
def baseStart_995960 : Nat := 118140960795 + 995960 * 2 ^ 59
def prefixEnd_995960 : Nat := 4983230072969 + 3 ^ 40 * 995960 * 2
def baseEnd_995960 : Nat := 170468730884009511873223

theorem tailTrace_995960 : CollatzResearch.WordTrace tailWord_995960 prefixEnd_995960 170468730884009511873223 := by
  unfold tailWord_995960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18162822735907245635520667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24217096981209660847360889 18162822735907245635520667)
  ·
    refine ⟨27244234103860868453281001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18162822735907245635520667 27244234103860868453281001)
    ·
      refine ⟨20433175577895651339960751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27244234103860868453281001 20433175577895651339960751)
      ·
        refine ⟨30649763366843477009941127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20433175577895651339960751 30649763366843477009941127)
        ·
          refine ⟨45974645050265215514911691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30649763366843477009941127 45974645050265215514911691)
          ·
            refine ⟨68961967575397823272367537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45974645050265215514911691 68961967575397823272367537)
            ·
              refine ⟨51721475681548367454275653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68961967575397823272367537 51721475681548367454275653)
              ·
                refine ⟨9697776690290318897676685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51721475681548367454275653 9697776690290318897676685)
                ·
                  refine ⟨3636666258858869586628757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9697776690290318897676685 3636666258858869586628757)
                  ·
                    refine ⟨170468730884009511873223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3636666258858869586628757 170468730884009511873223)
                    ·
                      rfl

theorem cell23_995960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_995960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995960 prefixEnd_995960 := by exact prefixLift 995960
  have htrace : WordTrace (prefixWord ++ tailWord_995960) baseStart_995960 baseEnd_995960 := by
    simpa [prefixWord, tailWord_995960, baseEnd_995960] using wordTrace_append hprefix tailTrace_995960
  have hstable : (prefixWord ++ tailWord_995960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995960).length < 2 ^ (prefixWord ++ tailWord_995960).sum := by decide
  have hdescent : baseEnd_995960 < baseStart_995960 := by decide
  rcases family_descends (prefixWord ++ tailWord_995960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995961 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 3]
def baseStart_995961 : Nat := 118140960795 + 995961 * 2 ^ 59
def prefixEnd_995961 : Nat := 4983230072969 + 3 ^ 40 * 995961 * 2
def baseEnd_995961 : Nat := 511406706132683031707165

theorem tailTrace_995961 : CollatzResearch.WordTrace tailWord_995961 prefixEnd_995961 511406706132683031707165 := by
  unfold tailWord_995961
  simp only [CollatzResearch.WordTrace]
  refine ⟨36325681944810868441827737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24217121296540578961218491 36325681944810868441827737)
  ·
    refine ⟨27244261458608151331370803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36325681944810868441827737 27244261458608151331370803)
    ·
      refine ⟨40866392187912226997056205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27244261458608151331370803 40866392187912226997056205)
      ·
        refine ⟨15324897070467085123896077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40866392187912226997056205 15324897070467085123896077)
        ·
          refine ⟨5746836401425156921461029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15324897070467085123896077 5746836401425156921461029)
          ·
            refine ⟨1077531825267216922773943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5746836401425156921461029 1077531825267216922773943)
            ·
              refine ⟨1616297737900825384160915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077531825267216922773943 1616297737900825384160915)
              ·
                refine ⟨2424446606851238076241373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616297737900825384160915 2424446606851238076241373)
                ·
                  refine ⟨909167477569214278590515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2424446606851238076241373 909167477569214278590515)
                  ·
                    refine ⟨1363751216353821417885773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 909167477569214278590515 1363751216353821417885773)
                    ·
                      refine ⟨511406706132683031707165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363751216353821417885773 511406706132683031707165)
                      ·
                        rfl

theorem cell23_995961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_995961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995961 prefixEnd_995961 := by exact prefixLift 995961
  have htrace : WordTrace (prefixWord ++ tailWord_995961) baseStart_995961 baseEnd_995961 := by
    simpa [prefixWord, tailWord_995961, baseEnd_995961] using wordTrace_append hprefix tailTrace_995961
  have hstable : (prefixWord ++ tailWord_995961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995961).length < 2 ^ (prefixWord ++ tailWord_995961).sum := by decide
  have hdescent : baseEnd_995961 < baseStart_995961 := by decide
  rcases family_descends (prefixWord ++ tailWord_995961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995967 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 2, 6, 2]
def baseStart_995967 : Nat := 118140960795 + 995967 * 2 ^ 59
def prefixEnd_995967 : Nat := 4983230072969 + 3 ^ 40 * 995967 * 2
def baseEnd_995967 : Nat := 511409787016610008232137

theorem tailTrace_995967 : CollatzResearch.WordTrace tailWord_995967 prefixEnd_995967 511409787016610008232137 := by
  unfold tailWord_995967
  simp only [CollatzResearch.WordTrace]
  refine ⟨36325900782789131466546155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24217267188526087644364103 36325900782789131466546155)
  ·
    refine ⟨54488851174183697199819233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36325900782789131466546155 54488851174183697199819233)
    ·
      refine ⟨40866638380637772899864425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54488851174183697199819233 40866638380637772899864425)
      ·
        refine ⟨30649978785478329674898319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40866638380637772899864425 30649978785478329674898319)
        ·
          refine ⟨45974968178217494512347479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30649978785478329674898319 45974968178217494512347479)
          ·
            refine ⟨68962452267326241768521219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45974968178217494512347479 68962452267326241768521219)
            ·
              refine ⟨103443678400989362652781829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68962452267326241768521219 103443678400989362652781829)
              ·
                refine ⟨19395689700185505497396593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103443678400989362652781829 19395689700185505497396593)
                ·
                  refine ⟨14546767275139129123047445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19395689700185505497396593 14546767275139129123047445)
                  ·
                    refine ⟨681879716022146677642849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14546767275139129123047445 681879716022146677642849)
                    ·
                      refine ⟨511409787016610008232137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681879716022146677642849 511409787016610008232137)
                      ·
                        rfl

theorem cell23_995967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_995967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995967 prefixEnd_995967 := by exact prefixLift 995967
  have htrace : WordTrace (prefixWord ++ tailWord_995967) baseStart_995967 baseEnd_995967 := by
    simpa [prefixWord, tailWord_995967, baseEnd_995967] using wordTrace_append hprefix tailTrace_995967
  have hstable : (prefixWord ++ tailWord_995967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995967).length < 2 ^ (prefixWord ++ tailWord_995967).sum := by decide
  have hdescent : baseEnd_995967 < baseStart_995967 := by decide
  rcases family_descends (prefixWord ++ tailWord_995967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995987 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 3]
def baseStart_995987 : Nat := 118140960795 + 995987 * 2 ^ 59
def prefixEnd_995987 : Nat := 4983230072969 + 3 ^ 40 * 995987 * 2
def baseEnd_995987 : Nat := 511420056629699929982045

theorem tailTrace_995987 : CollatzResearch.WordTrace tailWord_995987 prefixEnd_995987 511420056629699929982045 := by
  unfold tailWord_995987
  simp only [CollatzResearch.WordTrace]
  refine ⟨36326630242716674882274215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24217753495144449921516143 36326630242716674882274215)
  ·
    refine ⟨54489945364075012323411323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36326630242716674882274215 54489945364075012323411323)
    ·
      refine ⟨81734918046112518485116985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54489945364075012323411323 81734918046112518485116985)
      ·
        refine ⟨61301188534584388863837739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81734918046112518485116985 61301188534584388863837739)
        ·
          refine ⟨91951782801876583295756609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61301188534584388863837739 91951782801876583295756609)
          ·
            refine ⟨68963837101407437471817457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91951782801876583295756609 68963837101407437471817457)
            ·
              refine ⟨51722877826055578103863093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68963837101407437471817457 51722877826055578103863093)
              ·
                refine ⟨4849019796192710447237165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51722877826055578103863093 4849019796192710447237165)
                ·
                  refine ⟨1818382423572266417713937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4849019796192710447237165 1818382423572266417713937)
                  ·
                    refine ⟨1363786817679199813285453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1818382423572266417713937 1363786817679199813285453)
                    ·
                      refine ⟨511420056629699929982045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363786817679199813285453 511420056629699929982045)
                      ·
                        rfl

theorem cell23_995987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_995987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995987 prefixEnd_995987 := by exact prefixLift 995987
  have htrace : WordTrace (prefixWord ++ tailWord_995987) baseStart_995987 baseEnd_995987 := by
    simpa [prefixWord, tailWord_995987, baseEnd_995987] using wordTrace_append hprefix tailTrace_995987
  have hstable : (prefixWord ++ tailWord_995987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995987).length < 2 ^ (prefixWord ++ tailWord_995987).sum := by decide
  have hdescent : baseEnd_995987 < baseStart_995987 := by decide
  rcases family_descends (prefixWord ++ tailWord_995987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995988 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_995988 : Nat := 118140960795 + 995988 * 2 ^ 59
def prefixEnd_995988 : Nat := 4983230072969 + 3 ^ 40 * 995988 * 2
def baseEnd_995988 : Nat := 511420570110354426069541

theorem tailTrace_995988 : CollatzResearch.WordTrace tailWord_995988 prefixEnd_995988 511420570110354426069541 := by
  unfold tailWord_995988
  simp only [CollatzResearch.WordTrace]
  refine ⟨18163333357856526026530309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24217777810475368035373745 18163333357856526026530309)
  ·
    refine ⟨3405625004598098629974433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18163333357856526026530309 3405625004598098629974433)
    ·
      refine ⟨2554218753448573972480825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3405625004598098629974433 2554218753448573972480825)
      ·
        refine ⟨1915664065086430479360619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2554218753448573972480825 1915664065086430479360619)
        ·
          refine ⟨2873496097629645719040929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915664065086430479360619 2873496097629645719040929)
          ·
            refine ⟨2155122073222234289280697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2873496097629645719040929 2155122073222234289280697)
            ·
              refine ⟨1616341554916675716960523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2155122073222234289280697 1616341554916675716960523)
              ·
                refine ⟨2424512332375013575440785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616341554916675716960523 2424512332375013575440785)
                ·
                  refine ⟨1818384249281260181580589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2424512332375013575440785 1818384249281260181580589)
                  ·
                    refine ⟨681894093480472568092721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818384249281260181580589 681894093480472568092721)
                    ·
                      refine ⟨511420570110354426069541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681894093480472568092721 511420570110354426069541)
                      ·
                        rfl

theorem cell23_995988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_995988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995988 prefixEnd_995988 := by exact prefixLift 995988
  have htrace : WordTrace (prefixWord ++ tailWord_995988) baseStart_995988 baseEnd_995988 := by
    simpa [prefixWord, tailWord_995988, baseEnd_995988] using wordTrace_append hprefix tailTrace_995988
  have hstable : (prefixWord ++ tailWord_995988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995988).length < 2 ^ (prefixWord ++ tailWord_995988).sum := by decide
  have hdescent : baseEnd_995988 < baseStart_995988 := by decide
  rcases family_descends (prefixWord ++ tailWord_995988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995997 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_995997 : Nat := 118140960795 + 995997 * 2 ^ 59
def prefixEnd_995997 : Nat := 4983230072969 + 3 ^ 40 * 995997 * 2
def baseEnd_995997 : Nat := 511425191436244890856999

theorem tailTrace_995997 : CollatzResearch.WordTrace tailWord_995997 prefixEnd_995997 511425191436244890856999 := by
  unfold tailWord_995997
  simp only [CollatzResearch.WordTrace]
  refine ⟨36326994972680446590138245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24217996648453631060092163 36326994972680446590138245)
  ·
    refine ⟨6811311557377583735650921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36326994972680446590138245 6811311557377583735650921)
    ·
      refine ⟨5108483668033187801738191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6811311557377583735650921 5108483668033187801738191)
      ·
        refine ⟨7662725502049781702607287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5108483668033187801738191 7662725502049781702607287)
        ·
          refine ⟨11494088253074672553910931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7662725502049781702607287 11494088253074672553910931)
          ·
            refine ⟨17241132379612008830866397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11494088253074672553910931 17241132379612008830866397)
            ·
              refine ⟨6465424642354503311574899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17241132379612008830866397 6465424642354503311574899)
              ·
                refine ⟨9698136963531754967362349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465424642354503311574899 9698136963531754967362349)
                ·
                  refine ⟨3636801361324408112760881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9698136963531754967362349 3636801361324408112760881)
                  ·
                    refine ⟨2727601020993306084570661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3636801361324408112760881 2727601020993306084570661)
                    ·
                      refine ⟨511425191436244890856999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2727601020993306084570661 511425191436244890856999)
                      ·
                        rfl

theorem cell23_995997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_995997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_995997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_995997 prefixEnd_995997 := by exact prefixLift 995997
  have htrace : WordTrace (prefixWord ++ tailWord_995997) baseStart_995997 baseEnd_995997 := by
    simpa [prefixWord, tailWord_995997, baseEnd_995997] using wordTrace_append hprefix tailTrace_995997
  have hstable : (prefixWord ++ tailWord_995997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995997).length < 2 ^ (prefixWord ++ tailWord_995997).sum := by decide
  have hdescent : baseEnd_995997 < baseStart_995997 := by decide
  rcases family_descends (prefixWord ++ tailWord_995997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996007 : List Nat := [1, 1, 6, 3, 12]
def baseStart_996007 : Nat := 118140960795 + 996007 * 2 ^ 59
def prefixEnd_996007 : Nat := 4983230072969 + 3 ^ 40 * 996007 * 2
def baseEnd_996007 : Nat := 701550516108079357657

theorem tailTrace_996007 : CollatzResearch.WordTrace tailWord_996007 prefixEnd_996007 701550516108079357657 := by
  unfold tailWord_996007
  simp only [CollatzResearch.WordTrace]
  refine ⟨36327359702644218298002275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24218239801762812198668183 36327359702644218298002275)
  ·
    refine ⟨54491039553966327447003413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36327359702644218298002275 54491039553966327447003413)
    ·
      refine ⟨2554267479092171599078285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54491039553966327447003413 2554267479092171599078285)
      ·
        refine ⟨957850304659564349654357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2554267479092171599078285 957850304659564349654357)
        ·
          refine ⟨701550516108079357657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 957850304659564349654357 701550516108079357657)
          ·
            rfl

theorem cell23_996007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 12].length) (baseStart_996007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996007 prefixEnd_996007 := by exact prefixLift 996007
  have htrace : WordTrace (prefixWord ++ tailWord_996007) baseStart_996007 baseEnd_996007 := by
    simpa [prefixWord, tailWord_996007, baseEnd_996007] using wordTrace_append hprefix tailTrace_996007
  have hstable : (prefixWord ++ tailWord_996007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996007).length < 2 ^ (prefixWord ++ tailWord_996007).sum := by decide
  have hdescent : baseEnd_996007 < baseStart_996007 := by decide
  rcases family_descends (prefixWord ++ tailWord_996007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996052 : List Nat := [2, 4, 1, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_996052 : Nat := 118140960795 + 996052 * 2 ^ 59
def prefixEnd_996052 : Nat := 4983230072969 + 3 ^ 40 * 996052 * 2
def baseEnd_996052 : Nat := 511453432872242175669247

theorem tailTrace_996052 : CollatzResearch.WordTrace tailWord_996052 prefixEnd_996052 511453432872242175669247 := by
  unfold tailWord_996052
  simp only [CollatzResearch.WordTrace]
  refine ⟨18164500493740595491695205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24219333991654127322260273 18164500493740595491695205)
  ·
    refine ⟨3405843842576361654692851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18164500493740595491695205 3405843842576361654692851)
    ·
      refine ⟨5108765763864542482039277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405843842576361654692851 5108765763864542482039277)
      ·
        refine ⟨1915787161449203430764729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5108765763864542482039277 1915787161449203430764729)
        ·
          refine ⟨1436840371086902573073547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1915787161449203430764729 1436840371086902573073547)
          ·
            refine ⟨2155260556630353859610321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436840371086902573073547 2155260556630353859610321)
            ·
              refine ⟨1616445417472765394707741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2155260556630353859610321 1616445417472765394707741)
              ·
                refine ⟨606167031552287023015403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1616445417472765394707741 606167031552287023015403)
                ·
                  refine ⟨909250547328430534523105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606167031552287023015403 909250547328430534523105)
                  ·
                    refine ⟨681937910496322900892329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 909250547328430534523105 681937910496322900892329)
                    ·
                      refine ⟨511453432872242175669247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681937910496322900892329 511453432872242175669247)
                      ·
                        rfl

theorem cell23_996052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_996052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996052 prefixEnd_996052 := by exact prefixLift 996052
  have htrace : WordTrace (prefixWord ++ tailWord_996052) baseStart_996052 baseEnd_996052 := by
    simpa [prefixWord, tailWord_996052, baseEnd_996052] using wordTrace_append hprefix tailTrace_996052
  have hstable : (prefixWord ++ tailWord_996052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996052).length < 2 ^ (prefixWord ++ tailWord_996052).sum := by decide
  have hdescent : baseEnd_996052 < baseStart_996052 := by decide
  rcases family_descends (prefixWord ++ tailWord_996052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996068 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_996068 : Nat := 118140960795 + 996068 * 2 ^ 59
def prefixEnd_996068 : Nat := 4983230072969 + 3 ^ 40 * 996068 * 2
def baseEnd_996068 : Nat := 511461648562714113069173

theorem tailTrace_996068 : CollatzResearch.WordTrace tailWord_996068 prefixEnd_996068 511461648562714113069173 := by
  unfold tailWord_996068
  simp only [CollatzResearch.WordTrace]
  refine ⟨18164792277711612857986429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24219723036948817143981905 18164792277711612857986429)
  ·
    refine ⟨6811797104141854821744911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18164792277711612857986429 6811797104141854821744911)
    ·
      refine ⟨10217695656212782232617367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6811797104141854821744911 10217695656212782232617367)
      ·
        refine ⟨15326543484319173348926051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10217695656212782232617367 15326543484319173348926051)
        ·
          refine ⟨22989815226478760023389077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15326543484319173348926051 22989815226478760023389077)
          ·
            refine ⟨1077647588741191876096363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22989815226478760023389077 1077647588741191876096363)
            ·
              refine ⟨1616471383111787814144545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077647588741191876096363 1616471383111787814144545)
              ·
                refine ⟨1212353537333840860608409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616471383111787814144545 1212353537333840860608409)
                ·
                  refine ⟨909265153000380645456307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1212353537333840860608409 909265153000380645456307)
                  ·
                    refine ⟨1363897729500570968184461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 909265153000380645456307 1363897729500570968184461)
                    ·
                      refine ⟨511461648562714113069173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1363897729500570968184461 511461648562714113069173)
                      ·
                        rfl

theorem cell23_996068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_996068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996068 prefixEnd_996068 := by exact prefixLift 996068
  have htrace : WordTrace (prefixWord ++ tailWord_996068) baseStart_996068 baseEnd_996068 := by
    simpa [prefixWord, tailWord_996068, baseEnd_996068] using wordTrace_append hprefix tailTrace_996068
  have hstable : (prefixWord ++ tailWord_996068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996068).length < 2 ^ (prefixWord ++ tailWord_996068).sum := by decide
  have hdescent : baseEnd_996068 < baseStart_996068 := by decide
  rcases family_descends (prefixWord ++ tailWord_996068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996137 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_996137 : Nat := 118140960795 + 996137 * 2 ^ 59
def prefixEnd_996137 : Nat := 4983230072969 + 3 ^ 40 * 996137 * 2
def baseEnd_996137 : Nat := 511497078727874343106355

theorem tailTrace_996137 : CollatzResearch.WordTrace tailWord_996137 prefixEnd_996137 511497078727874343106355 := by
  unfold tailWord_996137
  simp only [CollatzResearch.WordTrace]
  refine ⟨36332101192173250500234665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24221400794782167000156443 36332101192173250500234665)
  ·
    refine ⟨27249075894129937875175999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36332101192173250500234665 27249075894129937875175999)
    ·
      refine ⟨40873613841194906812763999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27249075894129937875175999 40873613841194906812763999)
      ·
        refine ⟨61310420761792360219145999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40873613841194906812763999 61310420761792360219145999)
        ·
          refine ⟨91965631142688540328718999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61310420761792360219145999 91965631142688540328718999)
          ·
            refine ⟨137948446714032810493078499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91965631142688540328718999 137948446714032810493078499)
            ·
              refine ⟨206922670071049215739617749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137948446714032810493078499 206922670071049215739617749)
              ·
                refine ⟨4849750079790215993897291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206922670071049215739617749 4849750079790215993897291)
                ·
                  refine ⟨7274625119685323990845937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849750079790215993897291 7274625119685323990845937)
                  ·
                    refine ⟨5455968839763992993134453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7274625119685323990845937 5455968839763992993134453)
                    ·
                      refine ⟨511497078727874343106355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5455968839763992993134453 511497078727874343106355)
                      ·
                        rfl

theorem cell23_996137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_996137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996137 prefixEnd_996137 := by exact prefixLift 996137
  have htrace : WordTrace (prefixWord ++ tailWord_996137) baseStart_996137 baseEnd_996137 := by
    simpa [prefixWord, tailWord_996137, baseEnd_996137] using wordTrace_append hprefix tailTrace_996137
  have hstable : (prefixWord ++ tailWord_996137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996137).length < 2 ^ (prefixWord ++ tailWord_996137).sum := by decide
  have hdescent : baseEnd_996137 < baseStart_996137 := by decide
  rcases family_descends (prefixWord ++ tailWord_996137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996142 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_996142 : Nat := 118140960795 + 996142 * 2 ^ 59
def prefixEnd_996142 : Nat := 4983230072969 + 3 ^ 40 * 996142 * 2
def baseEnd_996142 : Nat := 511499646131146823543833

theorem tailTrace_996142 : CollatzResearch.WordTrace tailWord_996142 prefixEnd_996142 511499646131146823543833 := by
  unfold tailWord_996142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4541535444644392044270835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24221522371436757569444453 4541535444644392044270835)
  ·
    refine ⟨6812303166966588066406253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4541535444644392044270835 6812303166966588066406253)
    ·
      refine ⟨2554613687612470524902345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6812303166966588066406253 2554613687612470524902345)
      ·
        refine ⟨1915960265709352893676759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2554613687612470524902345 1915960265709352893676759)
        ·
          refine ⟨2873940398564029340515139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915960265709352893676759 2873940398564029340515139)
          ·
            refine ⟨4310910597846044010772709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873940398564029340515139 4310910597846044010772709)
            ·
              refine ⟨808295737096133252019883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4310910597846044010772709 808295737096133252019883)
              ·
                refine ⟨1212443605644199878029825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808295737096133252019883 1212443605644199878029825)
                ·
                  refine ⟨909332704233149908522369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1212443605644199878029825 909332704233149908522369)
                  ·
                    refine ⟨681999528174862431391777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 909332704233149908522369 681999528174862431391777)
                    ·
                      refine ⟨511499646131146823543833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 681999528174862431391777 511499646131146823543833)
                      ·
                        rfl

theorem cell23_996142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_996142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996142 prefixEnd_996142 := by exact prefixLift 996142
  have htrace : WordTrace (prefixWord ++ tailWord_996142) baseStart_996142 baseEnd_996142 := by
    simpa [prefixWord, tailWord_996142, baseEnd_996142] using wordTrace_append hprefix tailTrace_996142
  have hstable : (prefixWord ++ tailWord_996142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996142).length < 2 ^ (prefixWord ++ tailWord_996142).sum := by decide
  have hdescent : baseEnd_996142 < baseStart_996142 := by decide
  rcases family_descends (prefixWord ++ tailWord_996142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996181 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_996181 : Nat := 118140960795 + 996181 * 2 ^ 59
def prefixEnd_996181 : Nat := 4983230072969 + 3 ^ 40 * 996181 * 2
def baseEnd_996181 : Nat := 511519671876672170956153

theorem tailTrace_996181 : CollatzResearch.WordTrace tailWord_996181 prefixEnd_996181 511519671876672170956153 := by
  unfold tailWord_996181
  simp only [CollatzResearch.WordTrace]
  refine ⟨36333706004013846014836397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24222470669342564009890931 36333706004013846014836397)
  ·
    refine ⟨13625139751505192255563649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36333706004013846014836397 13625139751505192255563649)
    ·
      refine ⟨10218854813628894191672737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13625139751505192255563649 10218854813628894191672737)
      ·
        refine ⟨7664141110221670643754553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10218854813628894191672737 7664141110221670643754553)
        ·
          refine ⟨5748105832666252982815915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7664141110221670643754553 5748105832666252982815915)
          ·
            refine ⟨8622158748999379474223873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748105832666252982815915 8622158748999379474223873)
            ·
              refine ⟨6466619061749534605667905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8622158748999379474223873 6466619061749534605667905)
              ·
                refine ⟨4849964296312150954250929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6466619061749534605667905 4849964296312150954250929)
                ·
                  refine ⟨3637473222234113215688197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4849964296312150954250929 3637473222234113215688197)
                  ·
                    refine ⟨682026229168896227941537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3637473222234113215688197 682026229168896227941537)
                    ·
                      refine ⟨511519671876672170956153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682026229168896227941537 511519671876672170956153)
                      ·
                        rfl

theorem cell23_996181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_996181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996181 prefixEnd_996181 := by exact prefixLift 996181
  have htrace : WordTrace (prefixWord ++ tailWord_996181) baseStart_996181 baseEnd_996181 := by
    simpa [prefixWord, tailWord_996181, baseEnd_996181] using wordTrace_append hprefix tailTrace_996181
  have hstable : (prefixWord ++ tailWord_996181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996181).length < 2 ^ (prefixWord ++ tailWord_996181).sum := by decide
  have hdescent : baseEnd_996181 < baseStart_996181 := by decide
  rcases family_descends (prefixWord ++ tailWord_996181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996204 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 6]
def baseStart_996204 : Nat := 118140960795 + 996204 * 2 ^ 59
def prefixEnd_996204 : Nat := 4983230072969 + 3 ^ 40 * 996204 * 2
def baseEnd_996204 : Nat := 56836831325747286774283

theorem tailTrace_996204 : CollatzResearch.WordTrace tailWord_996204 prefixEnd_996204 56836831325747286774283 := by
  unfold tailWord_996204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18167272441465260471461833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24223029921953680628615777 18167272441465260471461833)
  ·
    refine ⟨13625454331098945353596375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18167272441465260471461833 13625454331098945353596375)
    ·
      refine ⟨20438181496648418030394563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13625454331098945353596375 20438181496648418030394563)
      ·
        refine ⟨30657272244972627045591845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20438181496648418030394563 30657272244972627045591845)
        ·
          refine ⟨5748238545932367571048471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30657272244972627045591845 5748238545932367571048471)
          ·
            refine ⟨8622357818898551356572707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748238545932367571048471 8622357818898551356572707)
            ·
              refine ⟨12933536728347827034859061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622357818898551356572707 12933536728347827034859061)
              ·
                refine ⟨1212519068282608784518037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12933536728347827034859061 1212519068282608784518037)
                ·
                  refine ⟨56836831325747286774283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1212519068282608784518037 56836831325747286774283)
                  ·
                    rfl

theorem cell23_996204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_996204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996204 prefixEnd_996204 := by exact prefixLift 996204
  have htrace : WordTrace (prefixWord ++ tailWord_996204) baseStart_996204 baseEnd_996204 := by
    simpa [prefixWord, tailWord_996204, baseEnd_996204] using wordTrace_append hprefix tailTrace_996204
  have hstable : (prefixWord ++ tailWord_996204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996204).length < 2 ^ (prefixWord ++ tailWord_996204).sum := by decide
  have hdescent : baseEnd_996204 < baseStart_996204 := by decide
  rcases family_descends (prefixWord ++ tailWord_996204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996241 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 4, 3, 2]
def baseStart_996241 : Nat := 118140960795 + 996241 * 2 ^ 59
def prefixEnd_996241 : Nat := 4983230072969 + 3 ^ 40 * 996241 * 2
def baseEnd_996241 : Nat := 511550480715941936205877

theorem tailTrace_996241 : CollatzResearch.WordTrace tailWord_996241 prefixEnd_996241 511550480715941936205877 := by
  unfold tailWord_996241
  simp only [CollatzResearch.WordTrace]
  refine ⟨36335894383796476262020577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24223929589197650841347051 36335894383796476262020577)
  ·
    refine ⟨27251920787847357196515433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36335894383796476262020577 27251920787847357196515433)
    ·
      refine ⟨20438940590885517897386575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27251920787847357196515433 20438940590885517897386575)
      ·
        refine ⟨30658410886328276846079863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20438940590885517897386575 30658410886328276846079863)
        ·
          refine ⟨45987616329492415269119795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30658410886328276846079863 45987616329492415269119795)
          ·
            refine ⟨68981424494238622903679693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45987616329492415269119795 68981424494238622903679693)
            ·
              refine ⟨25868034185339483588879885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68981424494238622903679693 25868034185339483588879885)
              ·
                refine ⟨9700512819502306345829957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25868034185339483588879885 9700512819502306345829957)
                ·
                  refine ⟨1818846153656682439843117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9700512819502306345829957 1818846153656682439843117)
                  ·
                    refine ⟨682067307621255914941169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818846153656682439843117 682067307621255914941169)
                    ·
                      refine ⟨511550480715941936205877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682067307621255914941169 511550480715941936205877)
                      ·
                        rfl

theorem cell23_996241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_996241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996241 prefixEnd_996241 := by exact prefixLift 996241
  have htrace : WordTrace (prefixWord ++ tailWord_996241) baseStart_996241 baseEnd_996241 := by
    simpa [prefixWord, tailWord_996241, baseEnd_996241] using wordTrace_append hprefix tailTrace_996241
  have hstable : (prefixWord ++ tailWord_996241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996241).length < 2 ^ (prefixWord ++ tailWord_996241).sum := by decide
  have hdescent : baseEnd_996241 < baseStart_996241 := by decide
  rcases family_descends (prefixWord ++ tailWord_996241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996258 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_996258 : Nat := 118140960795 + 996258 * 2 ^ 59
def prefixEnd_996258 : Nat := 4983230072969 + 3 ^ 40 * 996258 * 2
def baseEnd_996258 : Nat := 511559209887068369693299

theorem tailTrace_996258 : CollatzResearch.WordTrace tailWord_996258 prefixEnd_996258 511559209887068369693299 := by
  unfold tailWord_996258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084128606183722041347357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24224342949823258776926285 9084128606183722041347357)
  ·
    refine ⟨3406548227318895765505259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9084128606183722041347357 3406548227318895765505259)
    ·
      refine ⟨5109822340978343648257889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3406548227318895765505259 5109822340978343648257889)
      ·
        refine ⟨3832366755733757736193417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5109822340978343648257889 3832366755733757736193417)
        ·
          refine ⟨2874275066800318302145063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3832366755733757736193417 2874275066800318302145063)
          ·
            refine ⟨4311412600200477453217595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874275066800318302145063 4311412600200477453217595)
            ·
              refine ⟨6467118900300716179826393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4311412600200477453217595 6467118900300716179826393)
              ·
                refine ⟨4850339175225537134869795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6467118900300716179826393 4850339175225537134869795)
                ·
                  refine ⟨7275508762838305702304693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850339175225537134869795 7275508762838305702304693)
                  ·
                    refine ⟨682078946516091159591065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7275508762838305702304693 682078946516091159591065)
                    ·
                      refine ⟨511559209887068369693299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682078946516091159591065 511559209887068369693299)
                      ·
                        rfl

theorem cell23_996258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_996258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996258 prefixEnd_996258 := by exact prefixLift 996258
  have htrace : WordTrace (prefixWord ++ tailWord_996258) baseStart_996258 baseEnd_996258 := by
    simpa [prefixWord, tailWord_996258, baseEnd_996258] using wordTrace_append hprefix tailTrace_996258
  have hstable : (prefixWord ++ tailWord_996258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996258).length < 2 ^ (prefixWord ++ tailWord_996258).sum := by decide
  have hdescent : baseEnd_996258 < baseStart_996258 := by decide
  rcases family_descends (prefixWord ++ tailWord_996258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996281 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 4, 4]
def baseStart_996281 : Nat := 118140960795 + 996281 * 2 ^ 59
def prefixEnd_996281 : Nat := 4983230072969 + 3 ^ 40 * 996281 * 2
def baseEnd_996281 : Nat := 170523673314040593235231

theorem tailTrace_996281 : CollatzResearch.WordTrace tailWord_996281 prefixEnd_996281 170523673314040593235231 := by
  unfold tailWord_996281
  simp only [CollatzResearch.WordTrace]
  refine ⟨36337353303651563093476697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24224902202434375395651131 36337353303651563093476697)
  ·
    refine ⟨27253014977738672320107523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36337353303651563093476697 27253014977738672320107523)
    ·
      refine ⟨40879522466608008480161285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27253014977738672320107523 40879522466608008480161285)
      ·
        refine ⟨7664910462489001590030241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40879522466608008480161285 7664910462489001590030241)
        ·
          refine ⟨5748682846866751192522681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7664910462489001590030241 5748682846866751192522681)
          ·
            refine ⟨4311512135150063394392011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5748682846866751192522681 4311512135150063394392011)
            ·
              refine ⟨6467268202725095091588017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4311512135150063394392011 6467268202725095091588017)
              ·
                refine ⟨4850451152043821318691013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6467268202725095091588017 4850451152043821318691013)
                ·
                  refine ⟨909459591008216497254565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4850451152043821318691013 909459591008216497254565)
                  ·
                    refine ⟨170523673314040593235231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 909459591008216497254565 170523673314040593235231)
                    ·
                      rfl

theorem cell23_996281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 4].length) (baseStart_996281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996281 prefixEnd_996281 := by exact prefixLift 996281
  have htrace : WordTrace (prefixWord ++ tailWord_996281) baseStart_996281 baseEnd_996281 := by
    simpa [prefixWord, tailWord_996281, baseEnd_996281] using wordTrace_append hprefix tailTrace_996281
  have hstable : (prefixWord ++ tailWord_996281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996281).length < 2 ^ (prefixWord ++ tailWord_996281).sum := by decide
  have hdescent : baseEnd_996281 < baseStart_996281 := by decide
  rcases family_descends (prefixWord ++ tailWord_996281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996292 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_996292 : Nat := 118140960795 + 996292 * 2 ^ 59
def prefixEnd_996292 : Nat := 4983230072969 + 3 ^ 40 * 996292 * 2
def baseEnd_996292 : Nat := 511576668229321236668143

theorem tailTrace_996292 : CollatzResearch.WordTrace tailWord_996292 prefixEnd_996292 511576668229321236668143 := by
  unfold tailWord_996292
  simp only [CollatzResearch.WordTrace]
  refine ⟨18168877253305855986063565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24225169671074474648084753 18168877253305855986063565)
  ·
    refine ⟨6813328969989695994773837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18168877253305855986063565 6813328969989695994773837)
    ·
      refine ⟨2554998363746135998040189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6813328969989695994773837 2554998363746135998040189)
      ·
        refine ⟨958124386404800999265071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2554998363746135998040189 958124386404800999265071)
        ·
          refine ⟨1437186579607201498897607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958124386404800999265071 1437186579607201498897607)
          ·
            refine ⟨2155779869410802248346411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437186579607201498897607 2155779869410802248346411)
            ·
              refine ⟨3233669804116203372519617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155779869410802248346411 3233669804116203372519617)
              ·
                refine ⟨2425252353087152529389713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233669804116203372519617 2425252353087152529389713)
                ·
                  refine ⟨1818939264815364397042285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2425252353087152529389713 1818939264815364397042285)
                  ·
                    refine ⟨682102224305761648890857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818939264815364397042285 682102224305761648890857)
                    ·
                      refine ⟨511576668229321236668143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682102224305761648890857 511576668229321236668143)
                      ·
                        rfl

theorem cell23_996292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_996292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996292 prefixEnd_996292 := by exact prefixLift 996292
  have htrace : WordTrace (prefixWord ++ tailWord_996292) baseStart_996292 baseEnd_996292 := by
    simpa [prefixWord, tailWord_996292, baseEnd_996292] using wordTrace_append hprefix tailTrace_996292
  have hstable : (prefixWord ++ tailWord_996292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996292).length < 2 ^ (prefixWord ++ tailWord_996292).sum := by decide
  have hdescent : baseEnd_996292 < baseStart_996292 := by decide
  rcases family_descends (prefixWord ++ tailWord_996292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996321 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_996321 : Nat := 118140960795 + 996321 * 2 ^ 59
def prefixEnd_996321 : Nat := 4983230072969 + 3 ^ 40 * 996321 * 2
def baseEnd_996321 : Nat := 511591559168301623205509

theorem tailTrace_996321 : CollatzResearch.WordTrace tailWord_996321 prefixEnd_996321 511591559168301623205509 := by
  unfold tailWord_996321
  simp only [CollatzResearch.WordTrace]
  refine ⟨36338812223506649924932817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24225874815671099949955211 36338812223506649924932817)
  ·
    refine ⟨27254109167629987443699613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36338812223506649924932817 27254109167629987443699613)
    ·
      refine ⟨10220290937861245291387355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27254109167629987443699613 10220290937861245291387355)
      ·
        refine ⟨15330436406791867937081033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10220290937861245291387355 15330436406791867937081033)
        ·
          refine ⟨11497827305093900952810775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15330436406791867937081033 11497827305093900952810775)
          ·
            refine ⟨17246740957640851429216163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497827305093900952810775 17246740957640851429216163)
            ·
              refine ⟨25870111436461277143824245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17246740957640851429216163 25870111436461277143824245)
              ·
                refine ⟨2425322947168244732233523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25870111436461277143824245 2425322947168244732233523)
                ·
                  refine ⟨3637984420752367098350285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425322947168244732233523 3637984420752367098350285)
                  ·
                    refine ⟨1364244157782137661881357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637984420752367098350285 1364244157782137661881357)
                    ·
                      refine ⟨511591559168301623205509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1364244157782137661881357 511591559168301623205509)
                      ·
                        rfl

theorem cell23_996321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_996321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996321 prefixEnd_996321 := by exact prefixLift 996321
  have htrace : WordTrace (prefixWord ++ tailWord_996321) baseStart_996321 baseEnd_996321 := by
    simpa [prefixWord, tailWord_996321, baseEnd_996321] using wordTrace_append hprefix tailTrace_996321
  have hstable : (prefixWord ++ tailWord_996321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996321).length < 2 ^ (prefixWord ++ tailWord_996321).sum := by decide
  have hdescent : baseEnd_996321 < baseStart_996321 := by decide
  rcases family_descends (prefixWord ++ tailWord_996321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996322 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_996322 : Nat := 118140960795 + 996322 * 2 ^ 59
def prefixEnd_996322 : Nat := 4983230072969 + 3 ^ 40 * 996322 * 2
def baseEnd_996322 : Nat := 511592072648956119293005

theorem tailTrace_996322 : CollatzResearch.WordTrace tailWord_996322 prefixEnd_996322 511592072648956119293005 := by
  unfold tailWord_996322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084712174125756773929805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24225899131002018063812813 9084712174125756773929805)
  ·
    refine ⟨3406767065297158790223677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9084712174125756773929805 3406767065297158790223677)
    ·
      refine ⟨1277537649486434546333879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3406767065297158790223677 1277537649486434546333879)
      ·
        refine ⟨1916306474229651819500819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277537649486434546333879 1916306474229651819500819)
        ·
          refine ⟨2874459711344477729251229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916306474229651819500819 2874459711344477729251229)
          ·
            refine ⟨1077922391754179148469211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2874459711344477729251229 1077922391754179148469211)
            ·
              refine ⟨1616883587631268722703817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077922391754179148469211 1616883587631268722703817)
              ·
                refine ⟨1212662690723451542027863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616883587631268722703817 1212662690723451542027863)
                ·
                  refine ⟨1818994036085177313041795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212662690723451542027863 1818994036085177313041795)
                  ·
                    refine ⟨2728491054127765969562693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1818994036085177313041795 2728491054127765969562693)
                    ·
                      refine ⟨511592072648956119293005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2728491054127765969562693 511592072648956119293005)
                      ·
                        rfl

theorem cell23_996322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_996322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996322 prefixEnd_996322 := by exact prefixLift 996322
  have htrace : WordTrace (prefixWord ++ tailWord_996322) baseStart_996322 baseEnd_996322 := by
    simpa [prefixWord, tailWord_996322, baseEnd_996322] using wordTrace_append hprefix tailTrace_996322
  have hstable : (prefixWord ++ tailWord_996322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996322).length < 2 ^ (prefixWord ++ tailWord_996322).sum := by decide
  have hdescent : baseEnd_996322 < baseStart_996322 := by decide
  rcases family_descends (prefixWord ++ tailWord_996322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996324 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_996324 : Nat := 118140960795 + 996324 * 2 ^ 59
def prefixEnd_996324 : Nat := 4983230072969 + 3 ^ 40 * 996324 * 2
def baseEnd_996324 : Nat := 170531033203421703822665

theorem tailTrace_996324 : CollatzResearch.WordTrace tailWord_996324 prefixEnd_996324 170531033203421703822665 := by
  unfold tailWord_996324
  simp only [CollatzResearch.WordTrace]
  refine ⟨18169460821247890718646013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24225947761663854291528017 18169460821247890718646013)
  ·
    refine ⟨6813547807967959019492255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18169460821247890718646013 6813547807967959019492255)
    ·
      refine ⟨10220321711951938529238383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6813547807967959019492255 10220321711951938529238383)
      ·
        refine ⟨15330482567927907793857575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10220321711951938529238383 15330482567927907793857575)
        ·
          refine ⟨22995723851891861690786363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15330482567927907793857575 22995723851891861690786363)
          ·
            refine ⟨34493585777837792536179545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22995723851891861690786363 34493585777837792536179545)
            ·
              refine ⟨25870189333378344402134659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34493585777837792536179545 25870189333378344402134659)
              ·
                refine ⟨38805284000067516603201989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25870189333378344402134659 38805284000067516603201989)
                ·
                  refine ⟨7275990750012659363100373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38805284000067516603201989 7275990750012659363100373)
                  ·
                    refine ⟨170531033203421703822665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7275990750012659363100373 170531033203421703822665)
                    ·
                      rfl

theorem cell23_996324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_996324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996324 prefixEnd_996324 := by exact prefixLift 996324
  have htrace : WordTrace (prefixWord ++ tailWord_996324) baseStart_996324 baseEnd_996324 := by
    simpa [prefixWord, tailWord_996324, baseEnd_996324] using wordTrace_append hprefix tailTrace_996324
  have hstable : (prefixWord ++ tailWord_996324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996324).length < 2 ^ (prefixWord ++ tailWord_996324).sum := by decide
  have hdescent : baseEnd_996324 < baseStart_996324 := by decide
  rcases family_descends (prefixWord ++ tailWord_996324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996325 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 3]
def baseStart_996325 : Nat := 118140960795 + 996325 * 2 ^ 59
def prefixEnd_996325 : Nat := 4983230072969 + 3 ^ 40 * 996325 * 2
def baseEnd_996325 : Nat := 511593613090919607555491

theorem tailTrace_996325 : CollatzResearch.WordTrace tailWord_996325 prefixEnd_996325 511593613090919607555491 := by
  unfold tailWord_996325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36338958115492158608078429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24225972076994772405385619 36338958115492158608078429)
  ·
    refine ⟨13627109293309559478029411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36338958115492158608078429 13627109293309559478029411)
    ·
      refine ⟨20440663939964339217044117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13627109293309559478029411 20440663939964339217044117)
      ·
        refine ⟨958156122185828400798943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20440663939964339217044117 958156122185828400798943)
        ·
          refine ⟨1437234183278742601198415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958156122185828400798943 1437234183278742601198415)
          ·
            refine ⟨2155851274918113901797623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437234183278742601198415 2155851274918113901797623)
            ·
              refine ⟨3233776912377170852696435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155851274918113901797623 3233776912377170852696435)
              ·
                refine ⟨4850665368565756279044653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233776912377170852696435 4850665368565756279044653)
                ·
                  refine ⟨1818999513212158604641745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4850665368565756279044653 1818999513212158604641745)
                  ·
                    refine ⟨1364249634909118953481309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1818999513212158604641745 1364249634909118953481309)
                    ·
                      refine ⟨511593613090919607555491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1364249634909118953481309 511593613090919607555491)
                      ·
                        rfl

theorem cell23_996325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_996325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996325 prefixEnd_996325 := by exact prefixLift 996325
  have htrace : WordTrace (prefixWord ++ tailWord_996325) baseStart_996325 baseEnd_996325 := by
    simpa [prefixWord, tailWord_996325, baseEnd_996325] using wordTrace_append hprefix tailTrace_996325
  have hstable : (prefixWord ++ tailWord_996325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996325).length < 2 ^ (prefixWord ++ tailWord_996325).sum := by decide
  have hdescent : baseEnd_996325 < baseStart_996325 := by decide
  rcases family_descends (prefixWord ++ tailWord_996325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996342 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_996342 : Nat := 118140960795 + 996342 * 2 ^ 59
def prefixEnd_996342 : Nat := 4983230072969 + 3 ^ 40 * 996342 * 2
def baseEnd_996342 : Nat := 511602342262046041042913

theorem tailTrace_996342 : CollatzResearch.WordTrace tailWord_996342 prefixEnd_996342 511602342262046041042913 := by
  unfold tailWord_996342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271223634776910656965455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24226385437620380340964853 2271223634776910656965455)
  ·
    refine ⟨3406835452165365985448183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271223634776910656965455 3406835452165365985448183)
    ·
      refine ⟨5110253178248048978172275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3406835452165365985448183 5110253178248048978172275)
      ·
        refine ⟨7665379767372073467258413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110253178248048978172275 7665379767372073467258413)
        ·
          refine ⟨2874517412764527550221905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7665379767372073467258413 2874517412764527550221905)
          ·
            refine ⟨2155888059573395662666429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874517412764527550221905 2155888059573395662666429)
            ·
              refine ⟨808458022340023373499911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2155888059573395662666429 808458022340023373499911)
              ·
                refine ⟨1212687033510035060249867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808458022340023373499911 1212687033510035060249867)
                ·
                  refine ⟨1819030550265052590374801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212687033510035060249867 1819030550265052590374801)
                  ·
                    refine ⟨1364272912698789442781101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1819030550265052590374801 1364272912698789442781101)
                    ·
                      refine ⟨511602342262046041042913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1364272912698789442781101 511602342262046041042913)
                      ·
                        rfl

theorem cell23_996342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_996342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996342 prefixEnd_996342 := by exact prefixLift 996342
  have htrace : WordTrace (prefixWord ++ tailWord_996342) baseStart_996342 baseEnd_996342 := by
    simpa [prefixWord, tailWord_996342, baseEnd_996342] using wordTrace_append hprefix tailTrace_996342
  have hstable : (prefixWord ++ tailWord_996342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996342).length < 2 ^ (prefixWord ++ tailWord_996342).sum := by decide
  have hdescent : baseEnd_996342 < baseStart_996342 := by decide
  rcases family_descends (prefixWord ++ tailWord_996342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996412 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_996412 : Nat := 118140960795 + 996412 * 2 ^ 59
def prefixEnd_996412 : Nat := 4983230072969 + 3 ^ 40 * 996412 * 2
def baseEnd_996412 : Nat := 511638285907860767167591

theorem tailTrace_996412 : CollatzResearch.WordTrace tailWord_996412 prefixEnd_996412 511638285907860767167591 := by
  unfold tailWord_996412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18171065633088486233247745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24228087510784648310996993 18171065633088486233247745)
  ·
    refine ⟨13628299224816364674935809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18171065633088486233247745 13628299224816364674935809)
    ·
      refine ⟨10221224418612273506201857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13628299224816364674935809 10221224418612273506201857)
      ·
        refine ⟨7665918313959205129651393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10221224418612273506201857 7665918313959205129651393)
        ·
          refine ⟨5749438735469403847238545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7665918313959205129651393 5749438735469403847238545)
          ·
            refine ⟨4312079051602052885428909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5749438735469403847238545 4312079051602052885428909)
            ·
              refine ⟨1617029644350769832035841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4312079051602052885428909 1617029644350769832035841)
              ·
                refine ⟨1212772233263077374026881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617029644350769832035841 1212772233263077374026881)
                ·
                  refine ⟨909579174947308030520161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1212772233263077374026881 909579174947308030520161)
                  ·
                    refine ⟨682184381210481022890121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 909579174947308030520161 682184381210481022890121)
                    ·
                      refine ⟨511638285907860767167591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682184381210481022890121 511638285907860767167591)
                      ·
                        rfl

theorem cell23_996412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_996412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996412 prefixEnd_996412 := by exact prefixLift 996412
  have htrace : WordTrace (prefixWord ++ tailWord_996412) baseStart_996412 baseEnd_996412 := by
    simpa [prefixWord, tailWord_996412, baseEnd_996412] using wordTrace_append hprefix tailTrace_996412
  have hstable : (prefixWord ++ tailWord_996412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996412).length < 2 ^ (prefixWord ++ tailWord_996412).sum := by decide
  have hdescent : baseEnd_996412 < baseStart_996412 := by decide
  rcases family_descends (prefixWord ++ tailWord_996412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996469 : List Nat := [1, 3, 4, 3, 1, 1, 3, 2, 5]
def baseStart_996469 : Nat := 118140960795 + 996469 * 2 ^ 59
def prefixEnd_996469 : Nat := 4983230072969 + 3 ^ 40 * 996469 * 2
def baseEnd_996469 : Nat := 56851950478351893794981

theorem tailTrace_996469 : CollatzResearch.WordTrace tailWord_996469 prefixEnd_996469 56851950478351893794981 := by
  unfold tailWord_996469
  simp only [CollatzResearch.WordTrace]
  refine ⟨36344210226970471201320461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24229473484646980800880307 36344210226970471201320461)
  ·
    refine ⟨13629078835113926700495173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36344210226970471201320461 13629078835113926700495173)
    ·
      refine ⟨2555452281583861256342845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13629078835113926700495173 2555452281583861256342845)
      ·
        refine ⟨958294605593947971128567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2555452281583861256342845 958294605593947971128567)
        ·
          refine ⟨1437441908390921956692851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958294605593947971128567 1437441908390921956692851)
          ·
            refine ⟨2156162862586382935039277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437441908390921956692851 2156162862586382935039277)
            ·
              refine ⟨808561073469893600639729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2156162862586382935039277 808561073469893600639729)
              ·
                refine ⟨606420805102420200479797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808561073469893600639729 606420805102420200479797)
                ·
                  refine ⟨56851950478351893794981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 606420805102420200479797 56851950478351893794981)
                  ·
                    rfl

theorem cell23_996469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_996469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996469 prefixEnd_996469 := by exact prefixLift 996469
  have htrace : WordTrace (prefixWord ++ tailWord_996469) baseStart_996469 baseEnd_996469 := by
    simpa [prefixWord, tailWord_996469, baseEnd_996469] using wordTrace_append hprefix tailTrace_996469
  have hstable : (prefixWord ++ tailWord_996469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996469).length < 2 ^ (prefixWord ++ tailWord_996469).sum := by decide
  have hdescent : baseEnd_996469 < baseStart_996469 := by decide
  rcases family_descends (prefixWord ++ tailWord_996469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996522 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_996522 : Nat := 118140960795 + 996522 * 2 ^ 59
def prefixEnd_996522 : Nat := 4983230072969 + 3 ^ 40 * 996522 * 2
def baseEnd_996522 : Nat := 511694768779855336792085

theorem tailTrace_996522 : CollatzResearch.WordTrace tailWord_996522 prefixEnd_996522 511694768779855336792085 := by
  unfold tailWord_996522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9086535823944615313249955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24230762197185640835333213 9086535823944615313249955)
  ·
    refine ⟨13629803735916922969874933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9086535823944615313249955 13629803735916922969874933)
    ·
      refine ⟨1277794100242211528425775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13629803735916922969874933 1277794100242211528425775)
      ·
        refine ⟨1916691150363317292638663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277794100242211528425775 1916691150363317292638663)
        ·
          refine ⟨2875036725544975938957995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916691150363317292638663 2875036725544975938957995)
          ·
            refine ⟨4312555088317463908436993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875036725544975938957995 4312555088317463908436993)
            ·
              refine ⟨3234416316238097931327745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4312555088317463908436993 3234416316238097931327745)
              ·
                refine ⟨2425812237178573448495809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234416316238097931327745 2425812237178573448495809)
                ·
                  refine ⟨1819359177883930086371857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2425812237178573448495809 1819359177883930086371857)
                  ·
                    refine ⟨1364519383412947564778893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1819359177883930086371857 1364519383412947564778893)
                    ·
                      refine ⟨511694768779855336792085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1364519383412947564778893 511694768779855336792085)
                      ·
                        rfl

theorem cell23_996522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_996522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996522 prefixEnd_996522 := by exact prefixLift 996522
  have htrace : WordTrace (prefixWord ++ tailWord_996522) baseStart_996522 baseEnd_996522 := by
    simpa [prefixWord, tailWord_996522, baseEnd_996522] using wordTrace_append hprefix tailTrace_996522
  have hstable : (prefixWord ++ tailWord_996522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996522).length < 2 ^ (prefixWord ++ tailWord_996522).sum := by decide
  have hdescent : baseEnd_996522 < baseStart_996522 := by decide
  rcases family_descends (prefixWord ++ tailWord_996522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996529 : List Nat := [1, 2, 2, 5, 1, 1, 4, 2, 1, 4]
def baseStart_996529 : Nat := 118140960795 + 996529 * 2 ^ 59
def prefixEnd_996529 : Nat := 4983230072969 + 3 ^ 40 * 996529 * 2
def baseEnd_996529 : Nat := 170566121048145603134851

theorem tailTrace_996529 : CollatzResearch.WordTrace tailWord_996529 prefixEnd_996529 170566121048145603134851 := by
  unfold tailWord_996529
  simp only [CollatzResearch.WordTrace]
  refine ⟨36346398606753101448504641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24230932404502067632336427 36346398606753101448504641)
  ·
    refine ⟨27259798955064826086378481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36346398606753101448504641 27259798955064826086378481)
    ·
      refine ⟨20444849216298619564783861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27259798955064826086378481 20444849216298619564783861)
      ·
        refine ⟨1916704614027995584198487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20444849216298619564783861 1916704614027995584198487)
        ·
          refine ⟨2875056921041993376297731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916704614027995584198487 2875056921041993376297731)
          ·
            refine ⟨4312585381562990064446597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875056921041993376297731 4312585381562990064446597)
            ·
              refine ⟨808609759043060637083737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4312585381562990064446597 808609759043060637083737)
              ·
                refine ⟨606457319282295477812803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808609759043060637083737 606457319282295477812803)
                ·
                  refine ⟨909685978923443216719205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606457319282295477812803 909685978923443216719205)
                  ·
                    refine ⟨170566121048145603134851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 909685978923443216719205 170566121048145603134851)
                    ·
                      rfl

theorem cell23_996529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_996529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996529 prefixEnd_996529 := by exact prefixLift 996529
  have htrace : WordTrace (prefixWord ++ tailWord_996529) baseStart_996529 baseEnd_996529 := by
    simpa [prefixWord, tailWord_996529, baseEnd_996529] using wordTrace_append hprefix tailTrace_996529
  have hstable : (prefixWord ++ tailWord_996529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996529).length < 2 ^ (prefixWord ++ tailWord_996529).sum := by decide
  have hdescent : baseEnd_996529 < baseStart_996529 := by decide
  rcases family_descends (prefixWord ++ tailWord_996529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996535 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 3]
def baseStart_996535 : Nat := 118140960795 + 996535 * 2 ^ 59
def prefixEnd_996535 : Nat := 4983230072969 + 3 ^ 40 * 996535 * 2
def baseEnd_996535 : Nat := 511701444028363785929525

theorem tailTrace_996535 : CollatzResearch.WordTrace tailWord_996535 prefixEnd_996535 511701444028363785929525 := by
  unfold tailWord_996535
  simp only [CollatzResearch.WordTrace]
  refine ⟨36346617444731364473223059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24231078296487576315482039 36346617444731364473223059)
  ·
    refine ⟨54519926167097046709834589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36346617444731364473223059 54519926167097046709834589)
    ·
      refine ⟨20444972312661392516187971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54519926167097046709834589 20444972312661392516187971)
      ·
        refine ⟨30667458468992088774281957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20444972312661392516187971 30667458468992088774281957)
        ·
          refine ⟨5750148462936016645177867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30667458468992088774281957 5750148462936016645177867)
          ·
            refine ⟨8625222694404024967766801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750148462936016645177867 8625222694404024967766801)
            ·
              refine ⟨6468917020803018725825101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8625222694404024967766801 6468917020803018725825101)
              ·
                refine ⟨2425843882801132022184413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6468917020803018725825101 2425843882801132022184413)
                ·
                  refine ⟨909691456050424508319155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2425843882801132022184413 909691456050424508319155)
                  ·
                    refine ⟨1364537184075636762478733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 909691456050424508319155 1364537184075636762478733)
                    ·
                      refine ⟨511701444028363785929525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1364537184075636762478733 511701444028363785929525)
                      ·
                        rfl

theorem cell23_996535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_996535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996535 prefixEnd_996535 := by exact prefixLift 996535
  have htrace : WordTrace (prefixWord ++ tailWord_996535) baseStart_996535 baseEnd_996535 := by
    simpa [prefixWord, tailWord_996535, baseEnd_996535] using wordTrace_append hprefix tailTrace_996535
  have hstable : (prefixWord ++ tailWord_996535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996535).length < 2 ^ (prefixWord ++ tailWord_996535).sum := by decide
  have hdescent : baseEnd_996535 < baseStart_996535 := by decide
  rcases family_descends (prefixWord ++ tailWord_996535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996598 : List Nat := [5, 1, 1, 1, 1, 1, 1, 12]
def baseStart_996598 : Nat := 118140960795 + 996598 * 2 ^ 59
def prefixEnd_996598 : Nat := 4983230072969 + 3 ^ 40 * 996598 * 2
def baseEnd_996598 : Nat := 18953103455911001460805

theorem tailTrace_996598 : CollatzResearch.WordTrace tailWord_996598 prefixEnd_996598 18953103455911001460805 := by
  unfold tailWord_996598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271807202718945389547903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24232610162335417488510965 2271807202718945389547903)
  ·
    refine ⟨3407710804078418084321855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271807202718945389547903 3407710804078418084321855)
    ·
      refine ⟨5111566206117627126482783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407710804078418084321855 5111566206117627126482783)
      ·
        refine ⟨7667349309176440689724175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5111566206117627126482783 7667349309176440689724175)
        ·
          refine ⟨11501023963764661034586263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7667349309176440689724175 11501023963764661034586263)
          ·
            refine ⟨17251535945646991551879395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11501023963764661034586263 17251535945646991551879395)
            ·
              refine ⟨25877303918470487327819093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17251535945646991551879395 25877303918470487327819093)
              ·
                refine ⟨18953103455911001460805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 25877303918470487327819093 18953103455911001460805)
                ·
                  rfl

theorem cell23_996598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_996598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996598 prefixEnd_996598 := by exact prefixLift 996598
  have htrace : WordTrace (prefixWord ++ tailWord_996598) baseStart_996598 baseEnd_996598 := by
    simpa [prefixWord, tailWord_996598, baseEnd_996598] using wordTrace_append hprefix tailTrace_996598
  have hstable : (prefixWord ++ tailWord_996598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996598).length < 2 ^ (prefixWord ++ tailWord_996598).sum := by decide
  have hdescent : baseEnd_996598 < baseStart_996598 := by decide
  rcases family_descends (prefixWord ++ tailWord_996598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996602 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_996602 : Nat := 118140960795 + 996602 * 2 ^ 59
def prefixEnd_996602 : Nat := 4983230072969 + 3 ^ 40 * 996602 * 2
def baseEnd_996602 : Nat := 170578615744071674597239

theorem tailTrace_996602 : CollatzResearch.WordTrace tailWord_996602 prefixEnd_996602 170578615744071674597239 := by
  unfold tailWord_996602
  simp only [CollatzResearch.WordTrace]
  refine ⟨9087265283872158728978015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24232707423659089943941373 9087265283872158728978015)
  ·
    refine ⟨13630897925808238093467023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9087265283872158728978015 13630897925808238093467023)
    ·
      refine ⟨20446346888712357140200535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13630897925808238093467023 20446346888712357140200535)
      ·
        refine ⟨30669520333068535710300803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20446346888712357140200535 30669520333068535710300803)
        ·
          refine ⟨46004280499602803565451205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30669520333068535710300803 46004280499602803565451205)
          ·
            refine ⟨8625802593675525668522101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46004280499602803565451205 8625802593675525668522101)
            ·
              refine ⟨808668993157080531423947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8625802593675525668522101 808668993157080531423947)
              ·
                refine ⟨1213003489735620797135921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808668993157080531423947 1213003489735620797135921)
                ·
                  refine ⟨909752617301715597851941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1213003489735620797135921 909752617301715597851941)
                  ·
                    refine ⟨170578615744071674597239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 909752617301715597851941 170578615744071674597239)
                    ·
                      rfl

theorem cell23_996602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_996602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996602 prefixEnd_996602 := by exact prefixLift 996602
  have htrace : WordTrace (prefixWord ++ tailWord_996602) baseStart_996602 baseEnd_996602 := by
    simpa [prefixWord, tailWord_996602, baseEnd_996602] using wordTrace_append hprefix tailTrace_996602
  have hstable : (prefixWord ++ tailWord_996602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996602).length < 2 ^ (prefixWord ++ tailWord_996602).sum := by decide
  have hdescent : baseEnd_996602 < baseStart_996602 := by decide
  rcases family_descends (prefixWord ++ tailWord_996602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996612 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_996612 : Nat := 118140960795 + 996612 * 2 ^ 59
def prefixEnd_996612 : Nat := 4983230072969 + 3 ^ 40 * 996612 * 2
def baseEnd_996612 : Nat := 511740982038759984666671

theorem tailTrace_996612 : CollatzResearch.WordTrace tailWord_996612 prefixEnd_996612 511740982038759984666671 := by
  unfold tailWord_996612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18174712932726203311888045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24232950576968271082517393 18174712932726203311888045)
  ·
    refine ⟨6815517349772326241958017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18174712932726203311888045 6815517349772326241958017)
    ·
      refine ⟨5111638012329244681468513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6815517349772326241958017 5111638012329244681468513)
      ·
        refine ⟨3833728509246933511101385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5111638012329244681468513 3833728509246933511101385)
        ·
          refine ⟨2875296381935200133326039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3833728509246933511101385 2875296381935200133326039)
          ·
            refine ⟨4312944572902800199989059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875296381935200133326039 4312944572902800199989059)
            ·
              refine ⟨6469416859354200299983589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312944572902800199989059 6469416859354200299983589)
              ·
                refine ⟨1213015661128912556246923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6469416859354200299983589 1213015661128912556246923)
                ·
                  refine ⟨1819523491693368834370385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213015661128912556246923 1819523491693368834370385)
                  ·
                    refine ⟨1364642618770026625777789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1819523491693368834370385 1364642618770026625777789)
                    ·
                      refine ⟨511740982038759984666671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1364642618770026625777789 511740982038759984666671)
                      ·
                        rfl

theorem cell23_996612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_996612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996612 prefixEnd_996612 := by exact prefixLift 996612
  have htrace : WordTrace (prefixWord ++ tailWord_996612) baseStart_996612 baseEnd_996612 := by
    simpa [prefixWord, tailWord_996612, baseEnd_996612] using wordTrace_append hprefix tailTrace_996612
  have hstable : (prefixWord ++ tailWord_996612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996612).length < 2 ^ (prefixWord ++ tailWord_996612).sum := by decide
  have hdescent : baseEnd_996612 < baseStart_996612 := by decide
  rcases family_descends (prefixWord ++ tailWord_996612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996625 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 3]
def baseStart_996625 : Nat := 118140960795 + 996625 * 2 ^ 59
def prefixEnd_996625 : Nat := 4983230072969 + 3 ^ 40 * 996625 * 2
def baseEnd_996625 : Nat := 511747657287268433804111

theorem tailTrace_996625 : CollatzResearch.WordTrace tailWord_996625 prefixEnd_996625 511747657287268433804111 := by
  unfold tailWord_996625
  simp only [CollatzResearch.WordTrace]
  refine ⟨36349900014405309843999329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24233266676270206562666219 36349900014405309843999329)
  ·
    refine ⟨27262425010803982382999497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36349900014405309843999329 27262425010803982382999497)
    ·
      refine ⟨20446818758102986787249623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27262425010803982382999497 20446818758102986787249623)
      ·
        refine ⟨30670228137154480180874435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20446818758102986787249623 30670228137154480180874435)
        ·
          refine ⟨46005342205731720271311653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30670228137154480180874435 46005342205731720271311653)
          ·
            refine ⟨8626001663574697550870935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46005342205731720271311653 8626001663574697550870935)
            ·
              refine ⟨12939002495362046326306403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8626001663574697550870935 12939002495362046326306403)
              ·
                refine ⟨19408503743043069489459605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12939002495362046326306403 19408503743043069489459605)
                ·
                  refine ⟨909773612955143882318419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19408503743043069489459605 909773612955143882318419)
                  ·
                    refine ⟨1364660419432715823477629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 909773612955143882318419 1364660419432715823477629)
                    ·
                      refine ⟨511747657287268433804111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1364660419432715823477629 511747657287268433804111)
                      ·
                        rfl

theorem cell23_996625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_996625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996625 prefixEnd_996625 := by exact prefixLift 996625
  have htrace : WordTrace (prefixWord ++ tailWord_996625) baseStart_996625 baseEnd_996625 := by
    simpa [prefixWord, tailWord_996625, baseEnd_996625] using wordTrace_append hprefix tailTrace_996625
  have hstable : (prefixWord ++ tailWord_996625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996625).length < 2 ^ (prefixWord ++ tailWord_996625).sum := by decide
  have hdescent : baseEnd_996625 < baseStart_996625 := by decide
  rcases family_descends (prefixWord ++ tailWord_996625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996635 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 5, 3, 2]
def baseStart_996635 : Nat := 118140960795 + 996635 * 2 ^ 59
def prefixEnd_996635 : Nat := 4983230072969 + 3 ^ 40 * 996635 * 2
def baseEnd_996635 : Nat := 511752792093813394679065

theorem tailTrace_996635 : CollatzResearch.WordTrace tailWord_996635 prefixEnd_996635 511752792093813394679065 := by
  unfold tailWord_996635
  simp only [CollatzResearch.WordTrace]
  refine ⟨36350264744369081551863359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24233509829579387701242239 36350264744369081551863359)
  ·
    refine ⟨54525397116553622327795039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36350264744369081551863359 54525397116553622327795039)
    ·
      refine ⟨81788095674830433491692559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54525397116553622327795039 81788095674830433491692559)
      ·
        refine ⟨122682143512245650237538839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81788095674830433491692559 122682143512245650237538839)
        ·
          refine ⟨184023215268368475356308259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122682143512245650237538839 184023215268368475356308259)
          ·
            refine ⟨276034822902552713034462389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184023215268368475356308259 276034822902552713034462389)
            ·
              refine ⟨25878264647114316846980849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276034822902552713034462389 25878264647114316846980849)
              ·
                refine ⟨19408698485335737635235637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25878264647114316846980849 19408698485335737635235637)
                ·
                  refine ⟨1819565483000225403303341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19408698485335737635235637 1819565483000225403303341)
                  ·
                    refine ⟨682337056125084526238753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1819565483000225403303341 682337056125084526238753)
                    ·
                      refine ⟨511752792093813394679065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682337056125084526238753 511752792093813394679065)
                      ·
                        rfl

theorem cell23_996635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 3, 2].length) (baseStart_996635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996635 prefixEnd_996635 := by exact prefixLift 996635
  have htrace : WordTrace (prefixWord ++ tailWord_996635) baseStart_996635 baseEnd_996635 := by
    simpa [prefixWord, tailWord_996635, baseEnd_996635] using wordTrace_append hprefix tailTrace_996635
  have hstable : (prefixWord ++ tailWord_996635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996635).length < 2 ^ (prefixWord ++ tailWord_996635).sum := by decide
  have hdescent : baseEnd_996635 < baseStart_996635 := by decide
  rcases family_descends (prefixWord ++ tailWord_996635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996659 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 2, 1, 3]
def baseStart_996659 : Nat := 118140960795 + 996659 * 2 ^ 59
def prefixEnd_996659 : Nat := 4983230072969 + 3 ^ 40 * 996659 * 2
def baseEnd_996659 : Nat := 511765115629521300778955

theorem tailTrace_996659 : CollatzResearch.WordTrace tailWord_996659 prefixEnd_996659 511765115629521300778955 := by
  unfold tailWord_996659
  simp only [CollatzResearch.WordTrace]
  refine ⟨36351140096282133650737031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24234093397521422433824687 36351140096282133650737031)
  ·
    refine ⟨54526710144423200476105547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36351140096282133650737031 54526710144423200476105547)
    ·
      refine ⟨81790065216634800714158321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54526710144423200476105547 81790065216634800714158321)
      ·
        refine ⟨61342548912476100535618741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81790065216634800714158321 61342548912476100535618741)
        ·
          refine ⟨5750863960544634425214257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61342548912476100535618741 5750863960544634425214257)
          ·
            refine ⟨4313147970408475818910693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5750863960544634425214257 4313147970408475818910693)
            ·
              refine ⟨808715244451589216045755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4313147970408475818910693 808715244451589216045755)
              ·
                refine ⟨1213072866677383824068633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808715244451589216045755 1213072866677383824068633)
                ·
                  refine ⟨909804650008037868051475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1213072866677383824068633 909804650008037868051475)
                  ·
                    refine ⟨1364706975012056802077213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 909804650008037868051475 1364706975012056802077213)
                    ·
                      refine ⟨511765115629521300778955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1364706975012056802077213 511765115629521300778955)
                      ·
                        rfl

theorem cell23_996659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 1, 3].length) (baseStart_996659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996659 prefixEnd_996659 := by exact prefixLift 996659
  have htrace : WordTrace (prefixWord ++ tailWord_996659) baseStart_996659 baseEnd_996659 := by
    simpa [prefixWord, tailWord_996659, baseEnd_996659] using wordTrace_append hprefix tailTrace_996659
  have hstable : (prefixWord ++ tailWord_996659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996659).length < 2 ^ (prefixWord ++ tailWord_996659).sum := by decide
  have hdescent : baseEnd_996659 < baseStart_996659 := by decide
  rcases family_descends (prefixWord ++ tailWord_996659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996682 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_996682 : Nat := 118140960795 + 996682 * 2 ^ 59
def prefixEnd_996682 : Nat := 4983230072969 + 3 ^ 40 * 996682 * 2
def baseEnd_996682 : Nat := 511776925684574710791349

theorem tailTrace_996682 : CollatzResearch.WordTrace tailWord_996682 prefixEnd_996682 511776925684574710791349 := by
  unfold tailWord_996682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9087994743799702144706075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24234652650132539052549533 9087994743799702144706075)
  ·
    refine ⟨13631992115699553217059113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9087994743799702144706075 13631992115699553217059113)
    ·
      refine ⟨10223994086774664912794335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13631992115699553217059113 10223994086774664912794335)
      ·
        refine ⟨15335991130161997369191503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10223994086774664912794335 15335991130161997369191503)
        ·
          refine ⟨23003986695242996053787255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15335991130161997369191503 23003986695242996053787255)
          ·
            refine ⟨34505980042864494080680883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23003986695242996053787255 34505980042864494080680883)
            ·
              refine ⟨51758970064296741121021325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34505980042864494080680883 51758970064296741121021325)
              ·
                refine ⟨19409613774111277920382997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51758970064296741121021325 19409613774111277920382997)
                ·
                  refine ⟨909825645661466152517953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19409613774111277920382997 909825645661466152517953)
                  ·
                    refine ⟨682369234246099614388465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 909825645661466152517953 682369234246099614388465)
                    ·
                      refine ⟨511776925684574710791349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682369234246099614388465 511776925684574710791349)
                      ·
                        rfl

theorem cell23_996682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_996682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996682 prefixEnd_996682 := by exact prefixLift 996682
  have htrace : WordTrace (prefixWord ++ tailWord_996682) baseStart_996682 baseEnd_996682 := by
    simpa [prefixWord, tailWord_996682, baseEnd_996682] using wordTrace_append hprefix tailTrace_996682
  have hstable : (prefixWord ++ tailWord_996682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996682).length < 2 ^ (prefixWord ++ tailWord_996682).sum := by decide
  have hdescent : baseEnd_996682 < baseStart_996682 := by decide
  rcases family_descends (prefixWord ++ tailWord_996682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996698 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_996698 : Nat := 118140960795 + 996698 * 2 ^ 59
def prefixEnd_996698 : Nat := 4983230072969 + 3 ^ 40 * 996698 * 2
def baseEnd_996698 : Nat := 511785141375046648191275

theorem tailTrace_996698 : CollatzResearch.WordTrace tailWord_996698 prefixEnd_996698 511785141375046648191275 := by
  unfold tailWord_996698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9088140635785210827851687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24235041695427228874271165 9088140635785210827851687)
  ·
    refine ⟨13632210953677816241777531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9088140635785210827851687 13632210953677816241777531)
    ·
      refine ⟨20448316430516724362666297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13632210953677816241777531 20448316430516724362666297)
      ·
        refine ⟨15336237322887543271999723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20448316430516724362666297 15336237322887543271999723)
        ·
          refine ⟨23004355984331314907999585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15336237322887543271999723 23004355984331314907999585)
          ·
            refine ⟨17253266988248486180999689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23004355984331314907999585 17253266988248486180999689)
            ·
              refine ⟨12939950241186364635749767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17253266988248486180999689 12939950241186364635749767)
              ·
                refine ⟨19409925361779546953624651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12939950241186364635749767 19409925361779546953624651)
                ·
                  refine ⟨29114888042669320430436977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19409925361779546953624651 29114888042669320430436977)
                  ·
                    refine ⟨21836166032001990322827733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29114888042669320430436977 21836166032001990322827733)
                    ·
                      refine ⟨511785141375046648191275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21836166032001990322827733 511785141375046648191275)
                      ·
                        rfl

theorem cell23_996698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_996698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996698 prefixEnd_996698 := by exact prefixLift 996698
  have htrace : WordTrace (prefixWord ++ tailWord_996698) baseStart_996698 baseEnd_996698 := by
    simpa [prefixWord, tailWord_996698, baseEnd_996698] using wordTrace_append hprefix tailTrace_996698
  have hstable : (prefixWord ++ tailWord_996698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996698).length < 2 ^ (prefixWord ++ tailWord_996698).sum := by decide
  have hdescent : baseEnd_996698 < baseStart_996698 := by decide
  rcases family_descends (prefixWord ++ tailWord_996698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996712 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_996712 : Nat := 118140960795 + 996712 * 2 ^ 59
def prefixEnd_996712 : Nat := 4983230072969 + 3 ^ 40 * 996712 * 2
def baseEnd_996712 : Nat := 511792330104209593416211

theorem tailTrace_996712 : CollatzResearch.WordTrace tailWord_996712 prefixEnd_996712 511792330104209593416211 := by
  unfold tailWord_996712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18176536582545061851208195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24235382110060082468277593 18176536582545061851208195)
  ·
    refine ⟨27264804873817592776812293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18176536582545061851208195 27264804873817592776812293)
    ·
      refine ⟨5112150913840798645652305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27264804873817592776812293 5112150913840798645652305)
      ·
        refine ⟨3834113185380598984239229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5112150913840798645652305 3834113185380598984239229)
        ·
          refine ⟨1437792444517724619089711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3834113185380598984239229 1437792444517724619089711)
          ·
            refine ⟨2156688666776586928634567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437792444517724619089711 2156688666776586928634567)
            ·
              refine ⟨3235033000164880392951851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156688666776586928634567 3235033000164880392951851)
              ·
                refine ⟨4852549500247320589427777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235033000164880392951851 4852549500247320589427777)
                ·
                  refine ⟨3639412125185490442070833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4852549500247320589427777 3639412125185490442070833)
                  ·
                    refine ⟨2729559093889117831553125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3639412125185490442070833 2729559093889117831553125)
                    ·
                      refine ⟨511792330104209593416211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2729559093889117831553125 511792330104209593416211)
                      ·
                        rfl

theorem cell23_996712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_996712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996712 prefixEnd_996712 := by exact prefixLift 996712
  have htrace : WordTrace (prefixWord ++ tailWord_996712) baseStart_996712 baseEnd_996712 := by
    simpa [prefixWord, tailWord_996712, baseEnd_996712] using wordTrace_append hprefix tailTrace_996712
  have hstable : (prefixWord ++ tailWord_996712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996712).length < 2 ^ (prefixWord ++ tailWord_996712).sum := by decide
  have hdescent : baseEnd_996712 < baseStart_996712 := by decide
  rcases family_descends (prefixWord ++ tailWord_996712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996728 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_996728 : Nat := 118140960795 + 996728 * 2 ^ 59
def prefixEnd_996728 : Nat := 4983230072969 + 3 ^ 40 * 996728 * 2
def baseEnd_996728 : Nat := 511800545794681530816137

theorem tailTrace_996728 : CollatzResearch.WordTrace tailWord_996728 prefixEnd_996728 511800545794681530816137 := by
  unfold tailWord_996728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18176828366516079217499419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24235771155354772289999225 18176828366516079217499419)
  ·
    refine ⟨27265242549774118826249129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18176828366516079217499419 27265242549774118826249129)
    ·
      refine ⟨20448931912330589119686847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27265242549774118826249129 20448931912330589119686847)
      ·
        refine ⟨30673397868495883679530271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20448931912330589119686847 30673397868495883679530271)
        ·
          refine ⟨46010096802743825519295407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30673397868495883679530271 46010096802743825519295407)
          ·
            refine ⟨69015145204115738278943111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46010096802743825519295407 69015145204115738278943111)
            ·
              refine ⟨103522717806173607418414667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69015145204115738278943111 103522717806173607418414667)
              ·
                refine ⟨155284076709260411127622001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103522717806173607418414667 155284076709260411127622001)
                ·
                  refine ⟨116463057531945308345716501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155284076709260411127622001 116463057531945308345716501)
                  ·
                    refine ⟨5459205821809936328705461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116463057531945308345716501 5459205821809936328705461)
                    ·
                      refine ⟨511800545794681530816137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5459205821809936328705461 511800545794681530816137)
                      ·
                        rfl

theorem cell23_996728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_996728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996728 prefixEnd_996728 := by exact prefixLift 996728
  have htrace : WordTrace (prefixWord ++ tailWord_996728) baseStart_996728 baseEnd_996728 := by
    simpa [prefixWord, tailWord_996728, baseEnd_996728] using wordTrace_append hprefix tailTrace_996728
  have hstable : (prefixWord ++ tailWord_996728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996728).length < 2 ^ (prefixWord ++ tailWord_996728).sum := by decide
  have hdescent : baseEnd_996728 < baseStart_996728 := by decide
  rcases family_descends (prefixWord ++ tailWord_996728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996750 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_996750 : Nat := 118140960795 + 996750 * 2 ^ 59
def prefixEnd_996750 : Nat := 4983230072969 + 3 ^ 40 * 996750 * 2
def baseEnd_996750 : Nat := 511811842369080444741037

theorem tailTrace_996750 : CollatzResearch.WordTrace tailWord_996750 prefixEnd_996750 511811842369080444741037 := by
  unfold tailWord_996750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544307392369057024037463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24236306092634970794866469 4544307392369057024037463)
  ·
    refine ⟨6816461088553585536056195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4544307392369057024037463 6816461088553585536056195)
    ·
      refine ⟨10224691632830378304084293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6816461088553585536056195 10224691632830378304084293)
      ·
        refine ⟨1917129681155695932015805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10224691632830378304084293 1917129681155695932015805)
        ·
          refine ⟨718923630433385974505927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1917129681155695932015805 718923630433385974505927)
          ·
            refine ⟨1078385445650078961758891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718923630433385974505927 1078385445650078961758891)
            ·
              refine ⟨1617578168475118442638337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078385445650078961758891 1617578168475118442638337)
              ·
                refine ⟨1213183626356338831978753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617578168475118442638337 1213183626356338831978753)
                ·
                  refine ⟨909887719767254123984065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1213183626356338831978753 909887719767254123984065)
                  ·
                    refine ⟨682415789825440592988049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 909887719767254123984065 682415789825440592988049)
                    ·
                      refine ⟨511811842369080444741037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682415789825440592988049 511811842369080444741037)
                      ·
                        rfl

theorem cell23_996750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_996750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996750 prefixEnd_996750 := by exact prefixLift 996750
  have htrace : WordTrace (prefixWord ++ tailWord_996750) baseStart_996750 baseEnd_996750 := by
    simpa [prefixWord, tailWord_996750, baseEnd_996750] using wordTrace_append hprefix tailTrace_996750
  have hstable : (prefixWord ++ tailWord_996750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996750).length < 2 ^ (prefixWord ++ tailWord_996750).sum := by decide
  have hdescent : baseEnd_996750 < baseStart_996750 := by decide
  rcases family_descends (prefixWord ++ tailWord_996750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996785 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_996785 : Nat := 118140960795 + 996785 * 2 ^ 59
def prefixEnd_996785 : Nat := 4983230072969 + 3 ^ 40 * 996785 * 2
def baseEnd_996785 : Nat := 511829814191987807803375

theorem tailTrace_996785 : CollatzResearch.WordTrace tailWord_996785 prefixEnd_996785 511829814191987807803375 := by
  unfold tailWord_996785
  simp only [CollatzResearch.WordTrace]
  refine ⟨36355735693825657169823809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24237157129217104779882539 36355735693825657169823809)
  ·
    refine ⟨27266801770369242877367857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36355735693825657169823809 27266801770369242877367857)
    ·
      refine ⟨20450101327776932158025893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27266801770369242877367857 20450101327776932158025893)
      ·
        refine ⟨3834393998958174779629855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20450101327776932158025893 3834393998958174779629855)
        ·
          refine ⟨5751590998437262169444783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834393998958174779629855 5751590998437262169444783)
          ·
            refine ⟨8627386497655893254167175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751590998437262169444783 8627386497655893254167175)
            ·
              refine ⟨12941079746483839881250763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8627386497655893254167175 12941079746483839881250763)
              ·
                refine ⟨19411619619725759821876145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12941079746483839881250763 19411619619725759821876145)
                ·
                  refine ⟨14558714714794319866407109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19411619619725759821876145 14558714714794319866407109)
                  ·
                    refine ⟨2729759009023934974951333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14558714714794319866407109 2729759009023934974951333)
                    ·
                      refine ⟨511829814191987807803375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2729759009023934974951333 511829814191987807803375)
                      ·
                        rfl

theorem cell23_996785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_996785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996785 prefixEnd_996785 := by exact prefixLift 996785
  have htrace : WordTrace (prefixWord ++ tailWord_996785) baseStart_996785 baseEnd_996785 := by
    simpa [prefixWord, tailWord_996785, baseEnd_996785] using wordTrace_append hprefix tailTrace_996785
  have hstable : (prefixWord ++ tailWord_996785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996785).length < 2 ^ (prefixWord ++ tailWord_996785).sum := by decide
  have hdescent : baseEnd_996785 < baseStart_996785 := by decide
  rcases family_descends (prefixWord ++ tailWord_996785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996829 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 6]
def baseStart_996829 : Nat := 118140960795 + 996829 * 2 ^ 59
def prefixEnd_996829 : Nat := 4983230072969 + 3 ^ 40 * 996829 * 2
def baseEnd_996829 : Nat := 56872489704531737294797

theorem tailTrace_996829 : CollatzResearch.WordTrace tailWord_996829 prefixEnd_996829 56872489704531737294797 := by
  unfold tailWord_996829
  simp only [CollatzResearch.WordTrace]
  refine ⟨36357340505666252684425541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24238227003777501789617027 36357340505666252684425541)
  ·
    refine ⟨6817001344812422378329789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36357340505666252684425541 6817001344812422378329789)
    ·
      refine ⟨2556375504304658391873671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6817001344812422378329789 2556375504304658391873671)
      ·
        refine ⟨3834563256456987587810507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2556375504304658391873671 3834563256456987587810507)
        ·
          refine ⟨5751844884685481381715761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834563256456987587810507 5751844884685481381715761)
          ·
            refine ⟨4313883663514111036286821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5751844884685481381715761 4313883663514111036286821)
            ·
              refine ⟨808853186908895819303779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4313883663514111036286821 808853186908895819303779)
              ·
                refine ⟨1213279780363343728955669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808853186908895819303779 1213279780363343728955669)
                ·
                  refine ⟨56872489704531737294797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1213279780363343728955669 56872489704531737294797)
                  ·
                    rfl

theorem cell23_996829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_996829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996829 prefixEnd_996829 := by exact prefixLift 996829
  have htrace : WordTrace (prefixWord ++ tailWord_996829) baseStart_996829 baseEnd_996829 := by
    simpa [prefixWord, tailWord_996829, baseEnd_996829] using wordTrace_append hprefix tailTrace_996829
  have hstable : (prefixWord ++ tailWord_996829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996829).length < 2 ^ (prefixWord ++ tailWord_996829).sum := by decide
  have hdescent : baseEnd_996829 < baseStart_996829 := by decide
  rcases family_descends (prefixWord ++ tailWord_996829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996832 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 1, 5, 2]
def baseStart_996832 : Nat := 118140960795 + 996832 * 2 ^ 59
def prefixEnd_996832 : Nat := 4983230072969 + 3 ^ 40 * 996832 * 2
def baseEnd_996832 : Nat := 511853947782749123915659

theorem tailTrace_996832 : CollatzResearch.WordTrace tailWord_996832 prefixEnd_996832 511853947782749123915659 := by
  unfold tailWord_996832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18178724962327692098392375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24238299949770256131189833 18178724962327692098392375)
  ·
    refine ⟨27268087443491538147588563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18178724962327692098392375 27268087443491538147588563)
    ·
      refine ⟨40902131165237307221382845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27268087443491538147588563 40902131165237307221382845)
      ·
        refine ⟨15338299186963990208018567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40902131165237307221382845 15338299186963990208018567)
        ·
          refine ⟨23007448780445985312027851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15338299186963990208018567 23007448780445985312027851)
          ·
            refine ⟨34511173170668977968041777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23007448780445985312027851 34511173170668977968041777)
            ·
              refine ⟨25883379878001733476031333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34511173170668977968041777 25883379878001733476031333)
              ·
                refine ⟨4853133727125325026755875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25883379878001733476031333 4853133727125325026755875)
                ·
                  refine ⟨7279700590687987540133813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853133727125325026755875 7279700590687987540133813)
                  ·
                    refine ⟨682471930376998831887545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7279700590687987540133813 682471930376998831887545)
                    ·
                      refine ⟨511853947782749123915659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682471930376998831887545 511853947782749123915659)
                      ·
                        rfl

theorem cell23_996832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_996832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996832 prefixEnd_996832 := by exact prefixLift 996832
  have htrace : WordTrace (prefixWord ++ tailWord_996832) baseStart_996832 baseEnd_996832 := by
    simpa [prefixWord, tailWord_996832, baseEnd_996832] using wordTrace_append hprefix tailTrace_996832
  have hstable : (prefixWord ++ tailWord_996832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996832).length < 2 ^ (prefixWord ++ tailWord_996832).sum := by decide
  have hdescent : baseEnd_996832 < baseStart_996832 := by decide
  rcases family_descends (prefixWord ++ tailWord_996832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996849 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 2, 3, 2]
def baseStart_996849 : Nat := 118140960795 + 996849 * 2 ^ 59
def prefixEnd_996849 : Nat := 4983230072969 + 3 ^ 40 * 996849 * 2
def baseEnd_996849 : Nat := 511862676953875557403081

theorem tailTrace_996849 : CollatzResearch.WordTrace tailWord_996849 prefixEnd_996849 511862676953875557403081 := by
  unfold tailWord_996849
  simp only [CollatzResearch.WordTrace]
  refine ⟨36358069965593796100153601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24238713310395864066769067 36358069965593796100153601)
  ·
    refine ⟨27268552474195347075115201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36358069965593796100153601 27268552474195347075115201)
    ·
      refine ⟨20451414355646510306336401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27268552474195347075115201 20451414355646510306336401)
      ·
        refine ⟨15338560766734882729752301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20451414355646510306336401 15338560766734882729752301)
        ·
          refine ⟨5751960287525581023657113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15338560766734882729752301 5751960287525581023657113)
          ·
            refine ⟨4313970215644185767742835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5751960287525581023657113 4313970215644185767742835)
            ·
              refine ⟨6470955323466278651614253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313970215644185767742835 6470955323466278651614253)
              ·
                refine ⟨2426608246299854494355345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6470955323466278651614253 2426608246299854494355345)
                ·
                  refine ⟨1819956184724890870766509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2426608246299854494355345 1819956184724890870766509)
                  ·
                    refine ⟨682483569271834076537441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1819956184724890870766509 682483569271834076537441)
                    ·
                      refine ⟨511862676953875557403081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682483569271834076537441 511862676953875557403081)
                      ·
                        rfl

theorem cell23_996849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_996849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996849 prefixEnd_996849 := by exact prefixLift 996849
  have htrace : WordTrace (prefixWord ++ tailWord_996849) baseStart_996849 baseEnd_996849 := by
    simpa [prefixWord, tailWord_996849, baseEnd_996849] using wordTrace_append hprefix tailTrace_996849
  have hstable : (prefixWord ++ tailWord_996849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996849).length < 2 ^ (prefixWord ++ tailWord_996849).sum := by decide
  have hdescent : baseEnd_996849 < baseStart_996849 := by decide
  rcases family_descends (prefixWord ++ tailWord_996849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996872 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 4, 4]
def baseStart_996872 : Nat := 118140960795 + 996872 * 2 ^ 59
def prefixEnd_996872 : Nat := 4983230072969 + 3 ^ 40 * 996872 * 2
def baseEnd_996872 : Nat := 170624829002976322471825

theorem tailTrace_996872 : CollatzResearch.WordTrace tailWord_996872 prefixEnd_996872 170624829002976322471825 := by
  unfold tailWord_996872
  simp only [CollatzResearch.WordTrace]
  refine ⟨18179454422255235514120435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24239272563006980685493913 18179454422255235514120435)
  ·
    refine ⟨27269181633382853271180653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18179454422255235514120435 27269181633382853271180653)
    ·
      refine ⟨10225943112518569976692745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27269181633382853271180653 10225943112518569976692745)
      ·
        refine ⟨7669457334388927482519559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10225943112518569976692745 7669457334388927482519559)
        ·
          refine ⟨11504186001583391223779339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7669457334388927482519559 11504186001583391223779339)
          ·
            refine ⟨17256279002375086835669009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11504186001583391223779339 17256279002375086835669009)
            ·
              refine ⟨12942209251781315126751757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17256279002375086835669009 12942209251781315126751757)
              ·
                refine ⟨4853328469417993172531909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12942209251781315126751757 4853328469417993172531909)
                ·
                  refine ⟨909999088015873719849733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4853328469417993172531909 909999088015873719849733)
                  ·
                    refine ⟨170624829002976322471825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 909999088015873719849733 170624829002976322471825)
                    ·
                      rfl

theorem cell23_996872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_996872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996872 prefixEnd_996872 := by exact prefixLift 996872
  have htrace : WordTrace (prefixWord ++ tailWord_996872) baseStart_996872 baseEnd_996872 := by
    simpa [prefixWord, tailWord_996872, baseEnd_996872] using wordTrace_append hprefix tailTrace_996872
  have hstable : (prefixWord ++ tailWord_996872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996872).length < 2 ^ (prefixWord ++ tailWord_996872).sum := by decide
  have hdescent : baseEnd_996872 < baseStart_996872 := by decide
  rcases family_descends (prefixWord ++ tailWord_996872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996896 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 5, 2, 2]
def baseStart_996896 : Nat := 118140960795 + 996896 * 2 ^ 59
def prefixEnd_996896 : Nat := 4983230072969 + 3 ^ 40 * 996896 * 2
def baseEnd_996896 : Nat := 511886810544636873515365

theorem tailTrace_996896 : CollatzResearch.WordTrace tailWord_996896 prefixEnd_996896 511886810544636873515365 := by
  unfold tailWord_996896
  simp only [CollatzResearch.WordTrace]
  refine ⟨18179892098211761563557271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24239856130949015418076361 18179892098211761563557271)
  ·
    refine ⟨27269838147317642345335907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18179892098211761563557271 27269838147317642345335907)
    ·
      refine ⟨40904757220976463518003861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27269838147317642345335907 40904757220976463518003861)
      ·
        refine ⟨1917410494733271727406431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40904757220976463518003861 1917410494733271727406431)
        ·
          refine ⟨2876115742099907591109647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917410494733271727406431 2876115742099907591109647)
          ·
            refine ⟨4314173613149861386664471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876115742099907591109647 4314173613149861386664471)
            ·
              refine ⟨6471260419724792079996707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4314173613149861386664471 6471260419724792079996707)
              ·
                refine ⟨9706890629587188119995061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6471260419724792079996707 9706890629587188119995061)
                ·
                  refine ⟨910020996523798886249537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9706890629587188119995061 910020996523798886249537)
                  ·
                    refine ⟨682515747392849164687153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 910020996523798886249537 682515747392849164687153)
                    ·
                      refine ⟨511886810544636873515365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682515747392849164687153 511886810544636873515365)
                      ·
                        rfl

theorem cell23_996896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_996896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996896 prefixEnd_996896 := by exact prefixLift 996896
  have htrace : WordTrace (prefixWord ++ tailWord_996896) baseStart_996896 baseEnd_996896 := by
    simpa [prefixWord, tailWord_996896, baseEnd_996896] using wordTrace_append hprefix tailTrace_996896
  have hstable : (prefixWord ++ tailWord_996896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996896).length < 2 ^ (prefixWord ++ tailWord_996896).sum := by decide
  have hdescent : baseEnd_996896 < baseStart_996896 := by decide
  rcases family_descends (prefixWord ++ tailWord_996896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996946 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_996946 : Nat := 118140960795 + 996946 * 2 ^ 59
def prefixEnd_996946 : Nat := 4983230072969 + 3 ^ 40 * 996946 * 2
def baseEnd_996946 : Nat := 511912484577361677890135

theorem tailTrace_996946 : CollatzResearch.WordTrace tailWord_996946 prefixEnd_996946 511912484577361677890135 := by
  unfold tailWord_996946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9090401961560595416608673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24241071897494921110956461 9090401961560595416608673)
  ·
    refine ⟨6817801471170446562456505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9090401961560595416608673 6817801471170446562456505)
    ·
      refine ⟨5113351103377834921842379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6817801471170446562456505 5113351103377834921842379)
      ·
        refine ⟨7670026655066752382763569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5113351103377834921842379 7670026655066752382763569)
        ·
          refine ⟨5752519991300064287072677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7670026655066752382763569 5752519991300064287072677)
          ·
            refine ⟨1078597498368762053826127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5752519991300064287072677 1078597498368762053826127)
            ·
              refine ⟨1617896247553143080739191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078597498368762053826127 1617896247553143080739191)
              ·
                refine ⟨2426844371329714621108787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617896247553143080739191 2426844371329714621108787)
                ·
                  refine ⟨3640266556994571931663181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426844371329714621108787 3640266556994571931663181)
                  ·
                    refine ⟨1365099958872964474373693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640266556994571931663181 1365099958872964474373693)
                    ·
                      refine ⟨511912484577361677890135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1365099958872964474373693 511912484577361677890135)
                      ·
                        rfl

theorem cell23_996946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_996946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996946 prefixEnd_996946 := by exact prefixLift 996946
  have htrace : WordTrace (prefixWord ++ tailWord_996946) baseStart_996946 baseEnd_996946 := by
    simpa [prefixWord, tailWord_996946, baseEnd_996946] using wordTrace_append hprefix tailTrace_996946
  have hstable : (prefixWord ++ tailWord_996946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996946).length < 2 ^ (prefixWord ++ tailWord_996946).sum := by decide
  have hdescent : baseEnd_996946 < baseStart_996946 := by decide
  rcases family_descends (prefixWord ++ tailWord_996946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996969 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 1, 4, 2]
def baseStart_996969 : Nat := 118140960795 + 996969 * 2 ^ 59
def prefixEnd_996969 : Nat := 4983230072969 + 3 ^ 40 * 996969 * 2
def baseEnd_996969 : Nat := 511924294632415087902529

theorem tailTrace_996969 : CollatzResearch.WordTrace tailWord_996969 prefixEnd_996969 511924294632415087902529 := by
  unfold tailWord_996969
  simp only [CollatzResearch.WordTrace]
  refine ⟨36362446725159056594521961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24241631150106037729681307 36362446725159056594521961)
  ·
    refine ⟨27271835043869292445891471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36362446725159056594521961 27271835043869292445891471)
    ·
      refine ⟨40907752565803938668837207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27271835043869292445891471 40907752565803938668837207)
      ·
        refine ⟨61361628848705908003255811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40907752565803938668837207 61361628848705908003255811)
        ·
          refine ⟨92042443273058862004883717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61361628848705908003255811 92042443273058862004883717)
          ·
            refine ⟨17257958113698536625915697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92042443273058862004883717 17257958113698536625915697)
            ·
              refine ⟨12943468585273902469436773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17257958113698536625915697 12943468585273902469436773)
              ·
                refine ⟨2426900359738856713019395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12943468585273902469436773 2426900359738856713019395)
                ·
                  refine ⟨3640350539608285069529093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426900359738856713019395 3640350539608285069529093)
                  ·
                    refine ⟨682565726176553450536705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3640350539608285069529093 682565726176553450536705)
                    ·
                      refine ⟨511924294632415087902529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682565726176553450536705 511924294632415087902529)
                      ·
                        rfl

theorem cell23_996969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 4, 2].length) (baseStart_996969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996969 prefixEnd_996969 := by exact prefixLift 996969
  have htrace : WordTrace (prefixWord ++ tailWord_996969) baseStart_996969 baseEnd_996969 := by
    simpa [prefixWord, tailWord_996969, baseEnd_996969] using wordTrace_append hprefix tailTrace_996969
  have hstable : (prefixWord ++ tailWord_996969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996969).length < 2 ^ (prefixWord ++ tailWord_996969).sum := by decide
  have hdescent : baseEnd_996969 < baseStart_996969 := by decide
  rcases family_descends (prefixWord ++ tailWord_996969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_996972 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_996972 : Nat := 118140960795 + 996972 * 2 ^ 59
def prefixEnd_996972 : Nat := 4983230072969 + 3 ^ 40 * 996972 * 2
def baseEnd_996972 : Nat := 511925835074378576165015

theorem tailTrace_996972 : CollatzResearch.WordTrace tailWord_996972 prefixEnd_996972 511925835074378576165015 := by
  unfold tailWord_996972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18181278072074094053440585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24241704096098792071254113 18181278072074094053440585)
  ·
    refine ⟨13635958554055570540080439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18181278072074094053440585 13635958554055570540080439)
    ·
      refine ⟨20453937831083355810120659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13635958554055570540080439 20453937831083355810120659)
      ·
        refine ⟨30680906746625033715180989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20453937831083355810120659 30680906746625033715180989)
        ·
          refine ⟨11505340029984387643192871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30680906746625033715180989 11505340029984387643192871)
          ·
            refine ⟨17258010044976581464789307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11505340029984387643192871 17258010044976581464789307)
            ·
              refine ⟨25887015067464872197183961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17258010044976581464789307 25887015067464872197183961)
              ·
                refine ⟨19415261300598654147887971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25887015067464872197183961 19415261300598654147887971)
                ·
                  refine ⟨29122891950897981221831957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19415261300598654147887971 29122891950897981221831957)
                  ·
                    refine ⟨1365135560198342869773373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29122891950897981221831957 1365135560198342869773373)
                    ·
                      refine ⟨511925835074378576165015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1365135560198342869773373 511925835074378576165015)
                      ·
                        rfl

theorem cell23_996972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_996972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_996972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_996972 prefixEnd_996972 := by exact prefixLift 996972
  have htrace : WordTrace (prefixWord ++ tailWord_996972) baseStart_996972 baseEnd_996972 := by
    simpa [prefixWord, tailWord_996972, baseEnd_996972] using wordTrace_append hprefix tailTrace_996972
  have hstable : (prefixWord ++ tailWord_996972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_996972).length < 2 ^ (prefixWord ++ tailWord_996972).sum := by decide
  have hdescent : baseEnd_996972 < baseStart_996972 := by decide
  rcases family_descends (prefixWord ++ tailWord_996972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997072 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_997072 : Nat := 118140960795 + 997072 * 2 ^ 59
def prefixEnd_997072 : Nat := 4983230072969 + 3 ^ 40 * 997072 * 2
def baseEnd_997072 : Nat := 511977183139828184914555

theorem tailTrace_997072 : CollatzResearch.WordTrace tailWord_997072 prefixEnd_997072 511977183139828184914555 := by
  unfold tailWord_997072
  simp only [CollatzResearch.WordTrace]
  refine ⟨18183101721892952592760735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24244135629190603457014313 18183101721892952592760735)
  ·
    refine ⟨27274652582839428889141103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18183101721892952592760735 27274652582839428889141103)
    ·
      refine ⟨40911978874259143333711655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27274652582839428889141103 40911978874259143333711655)
      ·
        refine ⟨61367968311388715000567483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40911978874259143333711655 61367968311388715000567483)
        ·
          refine ⟨92051952467083072500851225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61367968311388715000567483 92051952467083072500851225)
          ·
            refine ⟨69038964350312304375638419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92051952467083072500851225 69038964350312304375638419)
            ·
              refine ⟨103558446525468456563457629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69038964350312304375638419 103558446525468456563457629)
              ·
                refine ⟨38834417447050671211296611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103558446525468456563457629 38834417447050671211296611)
                ·
                  refine ⟨58251626170576006816944917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38834417447050671211296611 58251626170576006816944917)
                  ·
                    refine ⟨2730544976745750319544293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58251626170576006816944917 2730544976745750319544293)
                    ·
                      refine ⟨511977183139828184914555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2730544976745750319544293 511977183139828184914555)
                      ·
                        rfl

theorem cell23_997072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_997072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997072 prefixEnd_997072 := by exact prefixLift 997072
  have htrace : WordTrace (prefixWord ++ tailWord_997072) baseStart_997072 baseEnd_997072 := by
    simpa [prefixWord, tailWord_997072, baseEnd_997072] using wordTrace_append hprefix tailTrace_997072
  have hstable : (prefixWord ++ tailWord_997072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997072).length < 2 ^ (prefixWord ++ tailWord_997072).sum := by decide
  have hdescent : baseEnd_997072 < baseStart_997072 := by decide
  rcases family_descends (prefixWord ++ tailWord_997072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997076 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_997076 : Nat := 118140960795 + 997076 * 2 ^ 59
def prefixEnd_997076 : Nat := 4983230072969 + 3 ^ 40 * 997076 * 2
def baseEnd_997076 : Nat := 511979237062446169264537

theorem tailTrace_997076 : CollatzResearch.WordTrace tailWord_997076 prefixEnd_997076 511979237062446169264537 := by
  unfold tailWord_997076
  simp only [CollatzResearch.WordTrace]
  refine ⟨18183174667885706934333541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24244232890514275912444721 18183174667885706934333541)
  ·
    refine ⟨3409345250228570050187539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18183174667885706934333541 3409345250228570050187539)
    ·
      refine ⟨5114017875342855075281309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3409345250228570050187539 5114017875342855075281309)
      ·
        refine ⟨1917756703253570653230491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5114017875342855075281309 1917756703253570653230491)
        ·
          refine ⟨2876635054880355979845737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917756703253570653230491 2876635054880355979845737)
          ·
            refine ⟨2157476291160266984884303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876635054880355979845737 2157476291160266984884303)
            ·
              refine ⟨3236214436740400477326455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157476291160266984884303 3236214436740400477326455)
              ·
                refine ⟨4854321655110600715989683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236214436740400477326455 4854321655110600715989683)
                ·
                  refine ⟨7281482482665901073984525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854321655110600715989683 7281482482665901073984525)
                  ·
                    refine ⟨2730555930999712902744197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7281482482665901073984525 2730555930999712902744197)
                    ·
                      refine ⟨511979237062446169264537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2730555930999712902744197 511979237062446169264537)
                      ·
                        rfl

theorem cell23_997076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_997076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997076 prefixEnd_997076 := by exact prefixLift 997076
  have htrace : WordTrace (prefixWord ++ tailWord_997076) baseStart_997076 baseEnd_997076 := by
    simpa [prefixWord, tailWord_997076, baseEnd_997076] using wordTrace_append hprefix tailTrace_997076
  have hstable : (prefixWord ++ tailWord_997076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997076).length < 2 ^ (prefixWord ++ tailWord_997076).sum := by decide
  have hdescent : baseEnd_997076 < baseStart_997076 := by decide
  rcases family_descends (prefixWord ++ tailWord_997076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997079 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_997079 : Nat := 118140960795 + 997079 * 2 ^ 59
def prefixEnd_997079 : Nat := 4983230072969 + 3 ^ 40 * 997079 * 2
def baseEnd_997079 : Nat := 511980777504409657527023

theorem tailTrace_997079 : CollatzResearch.WordTrace tailWord_997079 prefixEnd_997079 511980777504409657527023 := by
  unfold tailWord_997079
  simp only [CollatzResearch.WordTrace]
  refine ⟨36366458754760545381026291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24244305836507030254017527 36366458754760545381026291)
  ·
    refine ⟨54549688132140818071539437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36366458754760545381026291 54549688132140818071539437)
    ·
      refine ⟨20456133049552806776827289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54549688132140818071539437 20456133049552806776827289)
      ·
        refine ⟨15342099787164605082620467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20456133049552806776827289 15342099787164605082620467)
        ·
          refine ⟨23013149680746907623930701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15342099787164605082620467 23013149680746907623930701)
          ·
            refine ⟨8629931130280090358974013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23013149680746907623930701 8629931130280090358974013)
            ·
              refine ⟨3236224173855033884615255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8629931130280090358974013 3236224173855033884615255)
              ·
                refine ⟨4854336260782550826922883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236224173855033884615255 4854336260782550826922883)
                ·
                  refine ⟨7281504391173826240384325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854336260782550826922883 7281504391173826240384325)
                  ·
                    refine ⟨1365282073345092420072061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7281504391173826240384325 1365282073345092420072061)
                    ·
                      refine ⟨511980777504409657527023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1365282073345092420072061 511980777504409657527023)
                      ·
                        rfl

theorem cell23_997079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_997079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997079 prefixEnd_997079 := by exact prefixLift 997079
  have htrace : WordTrace (prefixWord ++ tailWord_997079) baseStart_997079 baseEnd_997079 := by
    simpa [prefixWord, tailWord_997079, baseEnd_997079] using wordTrace_append hprefix tailTrace_997079
  have hstable : (prefixWord ++ tailWord_997079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997079).length < 2 ^ (prefixWord ++ tailWord_997079).sum := by decide
  have hdescent : baseEnd_997079 < baseStart_997079 := by decide
  rcases family_descends (prefixWord ++ tailWord_997079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997099 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 6]
def baseStart_997099 : Nat := 118140960795 + 997099 * 2 ^ 59
def prefixEnd_997099 : Nat := 4983230072969 + 3 ^ 40 * 997099 * 2
def baseEnd_997099 : Nat := 56887894124166619919659

theorem tailTrace_997099 : CollatzResearch.WordTrace tailWord_997099 prefixEnd_997099 56887894124166619919659 := by
  unfold tailWord_997099
  simp only [CollatzResearch.WordTrace]
  refine ⟨36367188214688088796754351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24244792143125392531169567 36367188214688088796754351)
  ·
    refine ⟨54550782322032133195131527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36367188214688088796754351 54550782322032133195131527)
    ·
      refine ⟨81826173483048199792697291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54550782322032133195131527 81826173483048199792697291)
      ·
        refine ⟨122739260224572299689045937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81826173483048199792697291 122739260224572299689045937)
        ·
          refine ⟨92054445168429224766784453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122739260224572299689045937 92054445168429224766784453)
          ·
            refine ⟨17260208469080479643772085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92054445168429224766784453 17260208469080479643772085)
            ·
              refine ⟨1618144543976294966603633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17260208469080479643772085 1618144543976294966603633)
              ·
                refine ⟨1213608407982221224952725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1618144543976294966603633 1213608407982221224952725)
                ·
                  refine ⟨56887894124166619919659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1213608407982221224952725 56887894124166619919659)
                  ·
                    rfl

theorem cell23_997099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 6].length) (baseStart_997099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997099 prefixEnd_997099 := by exact prefixLift 997099
  have htrace : WordTrace (prefixWord ++ tailWord_997099) baseStart_997099 baseEnd_997099 := by
    simpa [prefixWord, tailWord_997099, baseEnd_997099] using wordTrace_append hprefix tailTrace_997099
  have hstable : (prefixWord ++ tailWord_997099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997099).length < 2 ^ (prefixWord ++ tailWord_997099).sum := by decide
  have hdescent : baseEnd_997099 < baseStart_997099 := by decide
  rcases family_descends (prefixWord ++ tailWord_997099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997112 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 2, 9]
def baseStart_997112 : Nat := 118140960795 + 997112 * 2 ^ 59
def prefixEnd_997112 : Nat := 4983230072969 + 3 ^ 40 * 997112 * 2
def baseEnd_997112 : Nat := 170665907455336009471457

theorem tailTrace_997112 : CollatzResearch.WordTrace tailWord_997112 prefixEnd_997112 170665907455336009471457 := by
  unfold tailWord_997112
  simp only [CollatzResearch.WordTrace]
  refine ⟨18183831181820496008488795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24245108242427328011318393 18183831181820496008488795)
  ·
    refine ⟨27275746772730744012733193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18183831181820496008488795 27275746772730744012733193)
    ·
      refine ⟨20456810079548058009549895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27275746772730744012733193 20456810079548058009549895)
      ·
        refine ⟨30685215119322087014324843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20456810079548058009549895 30685215119322087014324843)
        ·
          refine ⟨46027822678983130521487265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30685215119322087014324843 46027822678983130521487265)
          ·
            refine ⟨34520867009237347891115449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46027822678983130521487265 34520867009237347891115449)
            ·
              refine ⟨25890650256928010918336587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34520867009237347891115449 25890650256928010918336587)
              ·
                refine ⟨38835975385392016377504881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25890650256928010918336587 38835975385392016377504881)
                ·
                  refine ⟨29126981539044012283128661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38835975385392016377504881 29126981539044012283128661)
                  ·
                    refine ⟨170665907455336009471457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 29126981539044012283128661 170665907455336009471457)
                    ·
                      rfl

theorem cell23_997112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_997112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997112 prefixEnd_997112 := by exact prefixLift 997112
  have htrace : WordTrace (prefixWord ++ tailWord_997112) baseStart_997112 baseEnd_997112 := by
    simpa [prefixWord, tailWord_997112, baseEnd_997112] using wordTrace_append hprefix tailTrace_997112
  have hstable : (prefixWord ++ tailWord_997112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997112).length < 2 ^ (prefixWord ++ tailWord_997112).sum := by decide
  have hdescent : baseEnd_997112 < baseStart_997112 := by decide
  rcases family_descends (prefixWord ++ tailWord_997112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997116 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 6]
def baseStart_997116 : Nat := 118140960795 + 997116 * 2 ^ 59
def prefixEnd_997116 : Nat := 4983230072969 + 3 ^ 40 * 997116 * 2
def baseEnd_997116 : Nat := 56888864032069556973817

theorem tailTrace_997116 : CollatzResearch.WordTrace tailWord_997116 prefixEnd_997116 56888864032069556973817 := by
  unfold tailWord_997116
  simp only [CollatzResearch.WordTrace]
  refine ⟨18183904127813250350061601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24245205503751000466748801 18183904127813250350061601)
  ·
    refine ⟨13637928095859937762546201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18183904127813250350061601 13637928095859937762546201)
    ·
      refine ⟨10228446071894953321909651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13637928095859937762546201 10228446071894953321909651)
      ·
        refine ⟨15342669107842429982864477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10228446071894953321909651 15342669107842429982864477)
        ·
          refine ⟨5753500915440911243574179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15342669107842429982864477 5753500915440911243574179)
          ·
            refine ⟨8630251373161366865361269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753500915440911243574179 8630251373161366865361269)
            ·
              refine ⟨809086066233878143627619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8630251373161366865361269 809086066233878143627619)
              ·
                refine ⟨1213629099350817215441429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809086066233878143627619 1213629099350817215441429)
                ·
                  refine ⟨56888864032069556973817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1213629099350817215441429 56888864032069556973817)
                  ·
                    rfl

theorem cell23_997116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_997116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997116 prefixEnd_997116 := by exact prefixLift 997116
  have htrace : WordTrace (prefixWord ++ tailWord_997116) baseStart_997116 baseEnd_997116 := by
    simpa [prefixWord, tailWord_997116, baseEnd_997116] using wordTrace_append hprefix tailTrace_997116
  have hstable : (prefixWord ++ tailWord_997116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997116).length < 2 ^ (prefixWord ++ tailWord_997116).sum := by decide
  have hdescent : baseEnd_997116 < baseStart_997116 := by decide
  rcases family_descends (prefixWord ++ tailWord_997116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997146 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_997146 : Nat := 118140960795 + 997146 * 2 ^ 59
def prefixEnd_997146 : Nat := 4983230072969 + 3 ^ 40 * 997146 * 2
def baseEnd_997146 : Nat := 170671726902753631796405

theorem tailTrace_997146 : CollatzResearch.WordTrace tailWord_997146 prefixEnd_997146 170671726902753631796405 := by
  unfold tailWord_997146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9092225611379453955928823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24245934963678543882476861 9092225611379453955928823)
  ·
    refine ⟨13638338417069180933893235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9092225611379453955928823 13638338417069180933893235)
    ·
      refine ⟨20457507625603771400839853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13638338417069180933893235 20457507625603771400839853)
      ·
        refine ⟨7671565359601414275314945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20457507625603771400839853 7671565359601414275314945)
        ·
          refine ⟨5753674019701060706486209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7671565359601414275314945 5753674019701060706486209)
          ·
            refine ⟨4315255514775795529864657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5753674019701060706486209 4315255514775795529864657)
            ·
              refine ⟨3236441636081846647398493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4315255514775795529864657 3236441636081846647398493)
              ·
                refine ⟨1213665613530692492774435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3236441636081846647398493 1213665613530692492774435)
                ·
                  refine ⟨1820498420296038739161653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213665613530692492774435 1820498420296038739161653)
                  ·
                    refine ⟨170671726902753631796405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1820498420296038739161653 170671726902753631796405)
                    ·
                      rfl

theorem cell23_997146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_997146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997146 prefixEnd_997146 := by exact prefixLift 997146
  have htrace : WordTrace (prefixWord ++ tailWord_997146) baseStart_997146 baseEnd_997146 := by
    simpa [prefixWord, tailWord_997146, baseEnd_997146] using wordTrace_append hprefix tailTrace_997146
  have hstable : (prefixWord ++ tailWord_997146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997146).length < 2 ^ (prefixWord ++ tailWord_997146).sum := by decide
  have hdescent : baseEnd_997146 < baseStart_997146 := by decide
  rcases family_descends (prefixWord ++ tailWord_997146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997153 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_997153 : Nat := 118140960795 + 997153 * 2 ^ 59
def prefixEnd_997153 : Nat := 4983230072969 + 3 ^ 40 * 997153 * 2
def baseEnd_997153 : Nat := 512018775072842368001683

theorem tailTrace_997153 : CollatzResearch.WordTrace tailWord_997153 prefixEnd_997153 512018775072842368001683 := by
  unfold tailWord_997153
  simp only [CollatzResearch.WordTrace]
  refine ⟨36369157756492456019220113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24246105170994970679480075 36369157756492456019220113)
  ·
    refine ⟨27276868317369342014415085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36369157756492456019220113 27276868317369342014415085)
    ·
      refine ⟨10228825619013503255405657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27276868317369342014415085 10228825619013503255405657)
      ·
        refine ⟨7671619214260127441554243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10228825619013503255405657 7671619214260127441554243)
        ·
          refine ⟨11507428821390191162331365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7671619214260127441554243 11507428821390191162331365)
          ·
            refine ⟨2157642904010660842937131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11507428821390191162331365 2157642904010660842937131)
            ·
              refine ⟨3236464356015991264405697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157642904010660842937131 3236464356015991264405697)
              ·
                refine ⟨2427348267011993448304273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236464356015991264405697 2427348267011993448304273)
                ·
                  refine ⟨1820511200258995086228205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2427348267011993448304273 1820511200258995086228205)
                  ·
                    refine ⟨682691700097123157335577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1820511200258995086228205 682691700097123157335577)
                    ·
                      refine ⟨512018775072842368001683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682691700097123157335577 512018775072842368001683)
                      ·
                        rfl

theorem cell23_997153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_997153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997153 prefixEnd_997153 := by exact prefixLift 997153
  have htrace : WordTrace (prefixWord ++ tailWord_997153) baseStart_997153 baseEnd_997153 := by
    simpa [prefixWord, tailWord_997153, baseEnd_997153] using wordTrace_append hprefix tailTrace_997153
  have hstable : (prefixWord ++ tailWord_997153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997153).length < 2 ^ (prefixWord ++ tailWord_997153).sum := by decide
  have hdescent : baseEnd_997153 < baseStart_997153 := by decide
  rcases family_descends (prefixWord ++ tailWord_997153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997160 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_997160 : Nat := 118140960795 + 997160 * 2 ^ 59
def prefixEnd_997160 : Nat := 4983230072969 + 3 ^ 40 * 997160 * 2
def baseEnd_997160 : Nat := 512022369437423840614151

theorem tailTrace_997160 : CollatzResearch.WordTrace tailWord_997160 prefixEnd_997160 512022369437423840614151 := by
  unfold tailWord_997160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18184706533733548107362467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24246275378311397476483289 18184706533733548107362467)
  ·
    refine ⟨27277059800600322161043701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18184706533733548107362467 27277059800600322161043701)
    ·
      refine ⟨2557224356306280202597847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27277059800600322161043701 2557224356306280202597847)
      ·
        refine ⟨3835836534459420303896771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557224356306280202597847 3835836534459420303896771)
        ·
          refine ⟨5753754801689130455845157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835836534459420303896771 5753754801689130455845157)
          ·
            refine ⟨1078829025316711960470967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5753754801689130455845157 1078829025316711960470967)
            ·
              refine ⟨1618243537975067940706451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078829025316711960470967 1618243537975067940706451)
              ·
                refine ⟨2427365306962601911059677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618243537975067940706451 2427365306962601911059677)
                ·
                  refine ⟨910261990110975716647379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2427365306962601911059677 910261990110975716647379)
                  ·
                    refine ⟨1365392985166463574971069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 910261990110975716647379 1365392985166463574971069)
                    ·
                      refine ⟨512022369437423840614151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1365392985166463574971069 512022369437423840614151)
                      ·
                        rfl

theorem cell23_997160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_997160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997160 prefixEnd_997160 := by exact prefixLift 997160
  have htrace : WordTrace (prefixWord ++ tailWord_997160) baseStart_997160 baseEnd_997160 := by
    simpa [prefixWord, tailWord_997160, baseEnd_997160] using wordTrace_append hprefix tailTrace_997160
  have hstable : (prefixWord ++ tailWord_997160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997160).length < 2 ^ (prefixWord ++ tailWord_997160).sum := by decide
  have hdescent : baseEnd_997160 < baseStart_997160 := by decide
  rcases family_descends (prefixWord ++ tailWord_997160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997200 : List Nat := [2, 1, 1, 1, 1, 4, 1, 7, 1, 2, 2]
def baseStart_997200 : Nat := 118140960795 + 997200 * 2 ^ 59
def prefixEnd_997200 : Nat := 4983230072969 + 3 ^ 40 * 997200 * 2
def baseEnd_997200 : Nat := 512042908663603684113967

theorem tailTrace_997200 : CollatzResearch.WordTrace tailWord_997200 prefixEnd_997200 512042908663603684113967 := by
  unfold tailWord_997200
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185435993661091523090527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24247247991548122030787369 18185435993661091523090527)
  ·
    refine ⟨27278153990491637284635791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18185435993661091523090527 27278153990491637284635791)
    ·
      refine ⟨40917230985737455926953687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27278153990491637284635791 40917230985737455926953687)
      ·
        refine ⟨61375846478606183890430531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40917230985737455926953687 61375846478606183890430531)
        ·
          refine ⟨92063769717909275835645797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61375846478606183890430531 92063769717909275835645797)
          ·
            refine ⟨17261956822107989219183587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92063769717909275835645797 17261956822107989219183587)
            ·
              refine ⟨25892935233161983828775381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17261956822107989219183587 25892935233161983828775381)
              ·
                refine ⟨606865669527233995986923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25892935233161983828775381 606865669527233995986923)
                ·
                  refine ⟨910298504290850993980385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606865669527233995986923 910298504290850993980385)
                  ·
                    refine ⟨682723878218138245485289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 910298504290850993980385 682723878218138245485289)
                    ·
                      refine ⟨512042908663603684113967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682723878218138245485289 512042908663603684113967)
                      ·
                        rfl

theorem cell23_997200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 2, 2].length) (baseStart_997200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997200 prefixEnd_997200 := by exact prefixLift 997200
  have htrace : WordTrace (prefixWord ++ tailWord_997200) baseStart_997200 baseEnd_997200 := by
    simpa [prefixWord, tailWord_997200, baseEnd_997200] using wordTrace_append hprefix tailTrace_997200
  have hstable : (prefixWord ++ tailWord_997200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997200).length < 2 ^ (prefixWord ++ tailWord_997200).sum := by decide
  have hdescent : baseEnd_997200 < baseStart_997200 := by decide
  rcases family_descends (prefixWord ++ tailWord_997200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997233 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 3]
def baseStart_997233 : Nat := 118140960795 + 997233 * 2 ^ 59
def prefixEnd_997233 : Nat := 4983230072969 + 3 ^ 40 * 997233 * 2
def baseEnd_997233 : Nat := 512059853525202055001315

theorem tailTrace_997233 : CollatzResearch.WordTrace tailWord_997233 prefixEnd_997233 512059853525202055001315 := by
  unfold tailWord_997233
  simp only [CollatzResearch.WordTrace]
  refine ⟨36372075596202629682132353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24248050397468419788088235 36372075596202629682132353)
  ·
    refine ⟨27279056697151972261599265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36372075596202629682132353 27279056697151972261599265)
    ·
      refine ⟨20459292522863979196199449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27279056697151972261599265 20459292522863979196199449)
      ·
        refine ⟨15344469392147984397149587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20459292522863979196199449 15344469392147984397149587)
        ·
          refine ⟨23016704088221976595724381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15344469392147984397149587 23016704088221976595724381)
          ·
            refine ⟨8631264033083241223396643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23016704088221976595724381 8631264033083241223396643)
            ·
              refine ⟨12946896049624861835094965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631264033083241223396643 12946896049624861835094965)
              ·
                refine ⟨1213771504652330797040153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12946896049624861835094965 1213771504652330797040153)
                ·
                  refine ⟨910328628489248097780115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1213771504652330797040153 910328628489248097780115)
                  ·
                    refine ⟨1365492942733872146670173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 910328628489248097780115 1365492942733872146670173)
                    ·
                      refine ⟨512059853525202055001315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1365492942733872146670173 512059853525202055001315)
                      ·
                        rfl

theorem cell23_997233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_997233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997233 prefixEnd_997233 := by exact prefixLift 997233
  have htrace : WordTrace (prefixWord ++ tailWord_997233) baseStart_997233 baseEnd_997233 := by
    simpa [prefixWord, tailWord_997233, baseEnd_997233] using wordTrace_append hprefix tailTrace_997233
  have hstable : (prefixWord ++ tailWord_997233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997233).length < 2 ^ (prefixWord ++ tailWord_997233).sum := by decide
  have hdescent : baseEnd_997233 < baseStart_997233 := by decide
  rcases family_descends (prefixWord ++ tailWord_997233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997243 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 1, 3, 2]
def baseStart_997243 : Nat := 118140960795 + 997243 * 2 ^ 59
def prefixEnd_997243 : Nat := 4983230072969 + 3 ^ 40 * 997243 * 2
def baseEnd_997243 : Nat := 512064988331747015876269

theorem tailTrace_997243 : CollatzResearch.WordTrace tailWord_997243 prefixEnd_997243 512064988331747015876269 := by
  unfold tailWord_997243
  simp only [CollatzResearch.WordTrace]
  refine ⟨36372440326166401389996383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24248293550777600926664255 36372440326166401389996383)
  ·
    refine ⟨54558660489249602084994575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36372440326166401389996383 54558660489249602084994575)
    ·
      refine ⟨81837990733874403127491863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54558660489249602084994575 81837990733874403127491863)
      ·
        refine ⟨122756986100811604691237795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81837990733874403127491863 122756986100811604691237795)
        ·
          refine ⟨184135479151217407036856693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122756986100811604691237795 184135479151217407036856693)
          ·
            refine ⟨17262701170426631909705315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184135479151217407036856693 17262701170426631909705315)
            ·
              refine ⟨25894051755639947864557973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17262701170426631909705315 25894051755639947864557973)
              ·
                refine ⟨1213783676045622556151155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25894051755639947864557973 1213783676045622556151155)
                ·
                  refine ⟨1820675514068433834226733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213783676045622556151155 1820675514068433834226733)
                  ·
                    refine ⟨682753317775662687835025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1820675514068433834226733 682753317775662687835025)
                    ·
                      refine ⟨512064988331747015876269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682753317775662687835025 512064988331747015876269)
                      ·
                        rfl

theorem cell23_997243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 3, 2].length) (baseStart_997243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997243 prefixEnd_997243 := by exact prefixLift 997243
  have htrace : WordTrace (prefixWord ++ tailWord_997243) baseStart_997243 baseEnd_997243 := by
    simpa [prefixWord, tailWord_997243, baseEnd_997243] using wordTrace_append hprefix tailTrace_997243
  have hstable : (prefixWord ++ tailWord_997243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997243).length < 2 ^ (prefixWord ++ tailWord_997243).sum := by decide
  have hdescent : baseEnd_997243 < baseStart_997243 := by decide
  rcases family_descends (prefixWord ++ tailWord_997243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997259 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 5]
def baseStart_997259 : Nat := 118140960795 + 997259 * 2 ^ 59
def prefixEnd_997259 : Nat := 4983230072969 + 3 ^ 40 * 997259 * 2
def baseEnd_997259 : Nat := 512073204022218953276195

theorem tailTrace_997259 : CollatzResearch.WordTrace tailWord_997259 prefixEnd_997259 512073204022218953276195 := by
  unfold tailWord_997259
  simp only [CollatzResearch.WordTrace]
  refine ⟨36373023894108436122578831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24248682596072290748385887 36373023894108436122578831)
  ·
    refine ⟨54559535841162654183868247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36373023894108436122578831 54559535841162654183868247)
    ·
      refine ⟨81839303761743981275802371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54559535841162654183868247 81839303761743981275802371)
      ·
        refine ⟨122758955642615971913703557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81839303761743981275802371 122758955642615971913703557)
        ·
          refine ⟨23017304182990494733819417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122758955642615971913703557 23017304182990494733819417)
          ·
            refine ⟨17262978137242871050364563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23017304182990494733819417 17262978137242871050364563)
            ·
              refine ⟨25894467205864306575546845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17262978137242871050364563 25894467205864306575546845)
              ·
                refine ⟨9710425202199114965830067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25894467205864306575546845 9710425202199114965830067)
                ·
                  refine ⟨14565637803298672448745101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9710425202199114965830067 14565637803298672448745101)
                  ·
                    refine ⟨5462114176237002168279413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14565637803298672448745101 5462114176237002168279413)
                    ·
                      refine ⟨512073204022218953276195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5462114176237002168279413 512073204022218953276195)
                      ·
                        rfl

theorem cell23_997259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_997259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997259 prefixEnd_997259 := by exact prefixLift 997259
  have htrace : WordTrace (prefixWord ++ tailWord_997259) baseStart_997259 baseEnd_997259 := by
    simpa [prefixWord, tailWord_997259, baseEnd_997259] using wordTrace_append hprefix tailTrace_997259
  have hstable : (prefixWord ++ tailWord_997259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997259).length < 2 ^ (prefixWord ++ tailWord_997259).sum := by decide
  have hdescent : baseEnd_997259 < baseStart_997259 := by decide
  rcases family_descends (prefixWord ++ tailWord_997259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997306 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_997306 : Nat := 118140960795 + 997306 * 2 ^ 59
def prefixEnd_997306 : Nat := 4983230072969 + 3 ^ 40 * 997306 * 2
def baseEnd_997306 : Nat := 512097337612980269388479

theorem tailTrace_997306 : CollatzResearch.WordTrace tailWord_997306 prefixEnd_997306 512097337612980269388479 := by
  unfold tailWord_997306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093684531234540787384943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24249825416625442099693181 9093684531234540787384943)
  ·
    refine ⟨13640526796851811181077415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9093684531234540787384943 13640526796851811181077415)
    ·
      refine ⟨20460790195277716771616123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13640526796851811181077415 20460790195277716771616123)
      ·
        refine ⟨30691185292916575157424185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20460790195277716771616123 30691185292916575157424185)
        ·
          refine ⟨23018388969687431368068139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30691185292916575157424185 23018388969687431368068139)
          ·
            refine ⟨34527583454531147052102209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23018388969687431368068139 34527583454531147052102209)
            ·
              refine ⟨25895687590898360289076657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34527583454531147052102209 25895687590898360289076657)
              ·
                refine ⟨19421765693173770216807493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25895687590898360289076657 19421765693173770216807493)
                ·
                  refine ⟨3641581067470081915651405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19421765693173770216807493 3641581067470081915651405)
                  ·
                    refine ⟨1365592900301280718369277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641581067470081915651405 1365592900301280718369277)
                    ·
                      refine ⟨512097337612980269388479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1365592900301280718369277 512097337612980269388479)
                      ·
                        rfl

theorem cell23_997306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_997306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997306 prefixEnd_997306 := by exact prefixLift 997306
  have htrace : WordTrace (prefixWord ++ tailWord_997306) baseStart_997306 baseEnd_997306 := by
    simpa [prefixWord, tailWord_997306, baseEnd_997306] using wordTrace_append hprefix tailTrace_997306
  have hstable : (prefixWord ++ tailWord_997306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997306).length < 2 ^ (prefixWord ++ tailWord_997306).sum := by decide
  have hdescent : baseEnd_997306 < baseStart_997306 := by decide
  rcases family_descends (prefixWord ++ tailWord_997306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997330 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 7]
def baseStart_997330 : Nat := 118140960795 + 997330 * 2 ^ 59
def prefixEnd_997330 : Nat := 4983230072969 + 3 ^ 40 * 997330 * 2
def baseEnd_997330 : Nat := 56901073460965352832041

theorem tailTrace_997330 : CollatzResearch.WordTrace tailWord_997330 prefixEnd_997330 56901073460965352832041 := by
  unfold tailWord_997330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093903369212803812103361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24250408984567476832275629 9093903369212803812103361)
  ·
    refine ⟨6820427526909602859077521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9093903369212803812103361 6820427526909602859077521)
    ·
      refine ⟨5115320645182202144308141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6820427526909602859077521 5115320645182202144308141)
      ·
        refine ⟨1918245241943325804115553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5115320645182202144308141 1918245241943325804115553)
        ·
          refine ⟨1438683931457494353086665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1918245241943325804115553 1438683931457494353086665)
          ·
            refine ⟨1079012948593120764814999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1438683931457494353086665 1079012948593120764814999)
            ·
              refine ⟨1618519422889681147222499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079012948593120764814999 1618519422889681147222499)
              ·
                refine ⟨2427779134334521720833749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618519422889681147222499 2427779134334521720833749)
                ·
                  refine ⟨56901073460965352832041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2427779134334521720833749 56901073460965352832041)
                  ·
                    rfl

theorem cell23_997330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_997330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997330 prefixEnd_997330 := by exact prefixLift 997330
  have htrace : WordTrace (prefixWord ++ tailWord_997330) baseStart_997330 baseEnd_997330 := by
    simpa [prefixWord, tailWord_997330, baseEnd_997330] using wordTrace_append hprefix tailTrace_997330
  have hstable : (prefixWord ++ tailWord_997330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997330).length < 2 ^ (prefixWord ++ tailWord_997330).sum := by decide
  have hdescent : baseEnd_997330 < baseStart_997330 := by decide
  rcases family_descends (prefixWord ++ tailWord_997330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997336 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_997336 : Nat := 118140960795 + 997336 * 2 ^ 59
def prefixEnd_997336 : Nat := 4983230072969 + 3 ^ 40 * 997336 * 2
def baseEnd_997336 : Nat := 512112742032615152013341

theorem tailTrace_997336 : CollatzResearch.WordTrace tailWord_997336 prefixEnd_997336 512112742032615152013341 := by
  unfold tailWord_997336
  simp only [CollatzResearch.WordTrace]
  refine ⟨18187916157414739136565931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24250554876552985515421241 18187916157414739136565931)
  ·
    refine ⟨27281874236122108704848897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18187916157414739136565931 27281874236122108704848897)
    ·
      refine ⟨20461405677091581528636673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27281874236122108704848897 20461405677091581528636673)
      ·
        refine ⟨15346054257818686146477505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20461405677091581528636673 15346054257818686146477505)
        ·
          refine ⟨11509540693364014609858129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15346054257818686146477505 11509540693364014609858129)
          ·
            refine ⟨8632155520023010957393597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11509540693364014609858129 8632155520023010957393597)
            ·
              refine ⟨3237058320008629109022599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8632155520023010957393597 3237058320008629109022599)
              ·
                refine ⟨4855587480012943663533899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237058320008629109022599 4855587480012943663533899)
                ·
                  refine ⟨7283381220019415495300849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855587480012943663533899 7283381220019415495300849)
                  ·
                    refine ⟨5462535915014561621475637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7283381220019415495300849 5462535915014561621475637)
                    ·
                      refine ⟨512112742032615152013341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5462535915014561621475637 512112742032615152013341)
                      ·
                        rfl

theorem cell23_997336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_997336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997336 prefixEnd_997336 := by exact prefixLift 997336
  have htrace : WordTrace (prefixWord ++ tailWord_997336) baseStart_997336 baseEnd_997336 := by
    simpa [prefixWord, tailWord_997336, baseEnd_997336] using wordTrace_append hprefix tailTrace_997336
  have hstable : (prefixWord ++ tailWord_997336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997336).length < 2 ^ (prefixWord ++ tailWord_997336).sum := by decide
  have hdescent : baseEnd_997336 < baseStart_997336 := by decide
  rcases family_descends (prefixWord ++ tailWord_997336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997341 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_997341 : Nat := 118140960795 + 997341 * 2 ^ 59
def prefixEnd_997341 : Nat := 4983230072969 + 3 ^ 40 * 997341 * 2
def baseEnd_997341 : Nat := 512115309435887632450819

theorem tailTrace_997341 : CollatzResearch.WordTrace tailWord_997341 prefixEnd_997341 512115309435887632450819 := by
  unfold tailWord_997341
  simp only [CollatzResearch.WordTrace]
  refine ⟨36376014679811364127063877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24250676453207576084709251 36376014679811364127063877)
  ·
    refine ⟨6820502752464630773824477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36376014679811364127063877 6820502752464630773824477)
    ·
      refine ⟨2557688532174236540184179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6820502752464630773824477 2557688532174236540184179)
      ·
        refine ⟨3836532798261354810276269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557688532174236540184179 3836532798261354810276269)
        ·
          refine ⟨1438699799348008053853601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3836532798261354810276269 1438699799348008053853601)
          ·
            refine ⟨1079024849511006040390201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1438699799348008053853601 1079024849511006040390201)
            ·
              refine ⟨809268637133254530292651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079024849511006040390201 809268637133254530292651)
              ·
                refine ⟨1213902955699881795438977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809268637133254530292651 1213902955699881795438977)
                ·
                  refine ⟨910427216774911346579233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1213902955699881795438977 910427216774911346579233)
                  ·
                    refine ⟨682820412581183509934425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 910427216774911346579233 682820412581183509934425)
                    ·
                      refine ⟨512115309435887632450819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682820412581183509934425 512115309435887632450819)
                      ·
                        rfl

theorem cell23_997341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_997341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997341 prefixEnd_997341 := by exact prefixLift 997341
  have htrace : WordTrace (prefixWord ++ tailWord_997341) baseStart_997341 baseEnd_997341 := by
    simpa [prefixWord, tailWord_997341, baseEnd_997341] using wordTrace_append hprefix tailTrace_997341
  have hstable : (prefixWord ++ tailWord_997341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997341).length < 2 ^ (prefixWord ++ tailWord_997341).sum := by decide
  have hdescent : baseEnd_997341 < baseStart_997341 := by decide
  rcases family_descends (prefixWord ++ tailWord_997341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997447 : List Nat := [1, 1, 4, 1, 3, 1, 1, 6, 1, 1, 3]
def baseStart_997447 : Nat := 118140960795 + 997447 * 2 ^ 59
def prefixEnd_997447 : Nat := 4983230072969 + 3 ^ 40 * 997447 * 2
def baseEnd_997447 : Nat := 512169738385264217725331

theorem tailTrace_997447 : CollatzResearch.WordTrace tailWord_997447 prefixEnd_997447 512169738385264217725331 := by
  unfold tailWord_997447
  simp only [CollatzResearch.WordTrace]
  refine ⟨36379880817427344230422595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24253253878284896153615063 36379880817427344230422595)
  ·
    refine ⟨54569821226141016345633893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36379880817427344230422595 54569821226141016345633893)
    ·
      refine ⟨10231841479901440564806355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54569821226141016345633893 10231841479901440564806355)
      ·
        refine ⟨15347762219852160847209533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10231841479901440564806355 15347762219852160847209533)
        ·
          refine ⟨5755410832444560317703575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15347762219852160847209533 5755410832444560317703575)
          ·
            refine ⟨8633116248666840476555363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5755410832444560317703575 8633116248666840476555363)
            ·
              refine ⟨12949674373000260714833045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633116248666840476555363 12949674373000260714833045)
              ·
                refine ⟨607015986234387221007799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12949674373000260714833045 607015986234387221007799)
                ·
                  refine ⟨910523979351580831511699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 607015986234387221007799 910523979351580831511699)
                  ·
                    refine ⟨1365785969027371247267549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 910523979351580831511699 1365785969027371247267549)
                    ·
                      refine ⟨512169738385264217725331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1365785969027371247267549 512169738385264217725331)
                      ·
                        rfl

theorem cell23_997447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_997447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997447 prefixEnd_997447 := by exact prefixLift 997447
  have htrace : WordTrace (prefixWord ++ tailWord_997447) baseStart_997447 baseEnd_997447 := by
    simpa [prefixWord, tailWord_997447, baseEnd_997447] using wordTrace_append hprefix tailTrace_997447
  have hstable : (prefixWord ++ tailWord_997447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997447).length < 2 ^ (prefixWord ++ tailWord_997447).sum := by decide
  have hdescent : baseEnd_997447 < baseStart_997447 := by decide
  rcases family_descends (prefixWord ++ tailWord_997447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997463 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 1, 6]
def baseStart_997463 : Nat := 118140960795 + 997463 * 2 ^ 59
def prefixEnd_997463 : Nat := 4983230072969 + 3 ^ 40 * 997463 * 2
def baseEnd_997463 : Nat := 170725984691912051708419

theorem tailTrace_997463 : CollatzResearch.WordTrace tailWord_997463 prefixEnd_997463 170725984691912051708419 := by
  unfold tailWord_997463
  simp only [CollatzResearch.WordTrace]
  refine ⟨36380464385369378963005043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24253642923579585975336695 36380464385369378963005043)
  ·
    refine ⟨54570696578054068444507565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36380464385369378963005043 54570696578054068444507565)
    ·
      refine ⟨20464011216770275666690337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54570696578054068444507565 20464011216770275666690337)
      ·
        refine ⟨15348008412577706750017753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20464011216770275666690337 15348008412577706750017753)
        ·
          refine ⟨11511006309433280062513315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15348008412577706750017753 11511006309433280062513315)
          ·
            refine ⟨17266509464149920093769973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11511006309433280062513315 17266509464149920093769973)
            ·
              refine ⟨1618735262264055008790935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17266509464149920093769973 1618735262264055008790935)
              ·
                refine ⟨2428102893396082513186403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618735262264055008790935 2428102893396082513186403)
                ·
                  refine ⟨3642154340094123769779605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2428102893396082513186403 3642154340094123769779605)
                  ·
                    refine ⟨170725984691912051708419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3642154340094123769779605 170725984691912051708419)
                    ·
                      rfl

theorem cell23_997463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_997463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997463 prefixEnd_997463 := by exact prefixLift 997463
  have htrace : WordTrace (prefixWord ++ tailWord_997463) baseStart_997463 baseEnd_997463 := by
    simpa [prefixWord, tailWord_997463, baseEnd_997463] using wordTrace_append hprefix tailTrace_997463
  have hstable : (prefixWord ++ tailWord_997463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997463).length < 2 ^ (prefixWord ++ tailWord_997463).sum := by decide
  have hdescent : baseEnd_997463 < baseStart_997463 := by decide
  rcases family_descends (prefixWord ++ tailWord_997463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997490 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_997490 : Nat := 118140960795 + 997490 * 2 ^ 59
def prefixEnd_997490 : Nat := 4983230072969 + 3 ^ 40 * 997490 * 2
def baseEnd_997490 : Nat := 512191818053407549487633

theorem tailTrace_997490 : CollatzResearch.WordTrace tailWord_997490 prefixEnd_997490 512191818053407549487633 := by
  unfold tailWord_997490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9095362289067890643559481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24254299437514375049491949 9095362289067890643559481)
  ·
    refine ⟨6821521716800917982669611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9095362289067890643559481 6821521716800917982669611)
    ·
      refine ⟨10232282575201376974004417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6821521716800917982669611 10232282575201376974004417)
      ·
        refine ⟨7674211931401032730503313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10232282575201376974004417 7674211931401032730503313)
        ·
          refine ⟨5755658948550774547877485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7674211931401032730503313 5755658948550774547877485)
          ·
            refine ⟨2158372105706540455454057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5755658948550774547877485 2158372105706540455454057)
            ·
              refine ⟨1618779079279905341590543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2158372105706540455454057 1618779079279905341590543)
              ·
                refine ⟨2428168618919858012385815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618779079279905341590543 2428168618919858012385815)
                ·
                  refine ⟨3642252928379787018578723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2428168618919858012385815 3642252928379787018578723)
                  ·
                    refine ⟨5463379392569680527868085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3642252928379787018578723 5463379392569680527868085)
                    ·
                      refine ⟨512191818053407549487633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5463379392569680527868085 512191818053407549487633)
                      ·
                        rfl

theorem cell23_997490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_997490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997490 prefixEnd_997490 := by exact prefixLift 997490
  have htrace : WordTrace (prefixWord ++ tailWord_997490) baseStart_997490 baseEnd_997490 := by
    simpa [prefixWord, tailWord_997490, baseEnd_997490] using wordTrace_append hprefix tailTrace_997490
  have hstable : (prefixWord ++ tailWord_997490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997490).length < 2 ^ (prefixWord ++ tailWord_997490).sum := by decide
  have hdescent : baseEnd_997490 < baseStart_997490 := by decide
  rcases family_descends (prefixWord ++ tailWord_997490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997514 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_997514 : Nat := 118140960795 + 997514 * 2 ^ 59
def prefixEnd_997514 : Nat := 4983230072969 + 3 ^ 40 * 997514 * 2
def baseEnd_997514 : Nat := 170734713863038485195841

theorem tailTrace_997514 : CollatzResearch.WordTrace tailWord_997514 prefixEnd_997514 170734713863038485195841 := by
  unfold tailWord_997514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9095581127046153668277899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24254883005456409782074397 9095581127046153668277899)
  ·
    refine ⟨13643371690569230502416849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9095581127046153668277899 13643371690569230502416849)
    ·
      refine ⟨10232528767926922876812637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13643371690569230502416849 10232528767926922876812637)
      ·
        refine ⟨3837198287972596078804739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10232528767926922876812637 3837198287972596078804739)
        ·
          refine ⟨5755797431958894118207109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837198287972596078804739 5755797431958894118207109)
          ·
            refine ⟨1079212018492292647163833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5755797431958894118207109 1079212018492292647163833)
            ·
              refine ⟨809409013869219485372875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079212018492292647163833 809409013869219485372875)
              ·
                refine ⟨1214113520803829228059313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809409013869219485372875 1214113520803829228059313)
                ·
                  refine ⟨910585140602871921044485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1214113520803829228059313 910585140602871921044485)
                  ·
                    refine ⟨170734713863038485195841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 910585140602871921044485 170734713863038485195841)
                    ·
                      rfl

theorem cell23_997514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_997514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997514 prefixEnd_997514 := by exact prefixLift 997514
  have htrace : WordTrace (prefixWord ++ tailWord_997514) baseStart_997514 baseEnd_997514 := by
    simpa [prefixWord, tailWord_997514, baseEnd_997514] using wordTrace_append hprefix tailTrace_997514
  have hstable : (prefixWord ++ tailWord_997514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997514).length < 2 ^ (prefixWord ++ tailWord_997514).sum := by decide
  have hdescent : baseEnd_997514 < baseStart_997514 := by decide
  rcases family_descends (prefixWord ++ tailWord_997514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997524 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_997524 : Nat := 118140960795 + 997524 * 2 ^ 59
def prefixEnd_997524 : Nat := 4983230072969 + 3 ^ 40 * 997524 * 2
def baseEnd_997524 : Nat := 512209276395660416462477

theorem tailTrace_997524 : CollatzResearch.WordTrace tailWord_997524 prefixEnd_997524 512209276395660416462477 := by
  unfold tailWord_997524
  simp only [CollatzResearch.WordTrace]
  refine ⟨18191344619074193190487813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24255126158765590920650417 18191344619074193190487813)
  ·
    refine ⟨3410877116076411223216465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18191344619074193190487813 3410877116076411223216465)
    ·
      refine ⟨2558157837057308417412349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3410877116076411223216465 2558157837057308417412349)
      ·
        refine ⟨959309188896490656529631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2558157837057308417412349 959309188896490656529631)
        ·
          refine ⟨1438963783344735984794447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959309188896490656529631 1438963783344735984794447)
          ·
            refine ⟨2158445675017103977191671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438963783344735984794447 2158445675017103977191671)
            ·
              refine ⟨3237668512525655965787507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158445675017103977191671 3237668512525655965787507)
              ·
                refine ⟨4856502768788483948681261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237668512525655965787507 4856502768788483948681261)
                ·
                  refine ⟨1821188538295681480755473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4856502768788483948681261 1821188538295681480755473)
                  ·
                    refine ⟨1365891403721761110566605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1821188538295681480755473 1365891403721761110566605)
                    ·
                      refine ⟨512209276395660416462477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1365891403721761110566605 512209276395660416462477)
                      ·
                        rfl

theorem cell23_997524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_997524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997524 prefixEnd_997524 := by exact prefixLift 997524
  have htrace : WordTrace (prefixWord ++ tailWord_997524) baseStart_997524 baseEnd_997524 := by
    simpa [prefixWord, tailWord_997524, baseEnd_997524] using wordTrace_append hprefix tailTrace_997524
  have hstable : (prefixWord ++ tailWord_997524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997524).length < 2 ^ (prefixWord ++ tailWord_997524).sum := by decide
  have hdescent : baseEnd_997524 < baseStart_997524 := by decide
  rcases family_descends (prefixWord ++ tailWord_997524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997560 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 3, 4, 2]
def baseStart_997560 : Nat := 118140960795 + 997560 * 2 ^ 59
def prefixEnd_997560 : Nat := 4983230072969 + 3 ^ 40 * 997560 * 2
def baseEnd_997560 : Nat := 512227761699222275612311

theorem tailTrace_997560 : CollatzResearch.WordTrace tailWord_997560 prefixEnd_997560 512227761699222275612311 := by
  unfold tailWord_997560
  simp only [CollatzResearch.WordTrace]
  refine ⟨18192001133008982264643067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24256001510678643019524089 18192001133008982264643067)
  ·
    refine ⟨27288001699513473396964601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18192001133008982264643067 27288001699513473396964601)
    ·
      refine ⟨20466001274635105047723451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27288001699513473396964601 20466001274635105047723451)
      ·
        refine ⟨30699001911952657571585177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20466001274635105047723451 30699001911952657571585177)
        ·
          refine ⟨23024251433964493178688883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30699001911952657571585177 23024251433964493178688883)
          ·
            refine ⟨34536377150946739768033325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23024251433964493178688883 34536377150946739768033325)
            ·
              refine ⟨12951141431605027413012497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34536377150946739768033325 12951141431605027413012497)
              ·
                refine ⟨9713356073703770559759373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12951141431605027413012497 9713356073703770559759373)
                ·
                  refine ⟨3642508527638913959909765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9713356073703770559759373 3642508527638913959909765)
                  ·
                    refine ⟨682970348932296367483081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3642508527638913959909765 682970348932296367483081)
                    ·
                      refine ⟨512227761699222275612311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 682970348932296367483081 512227761699222275612311)
                      ·
                        rfl

theorem cell23_997560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_997560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997560 prefixEnd_997560 := by exact prefixLift 997560
  have htrace : WordTrace (prefixWord ++ tailWord_997560) baseStart_997560 baseEnd_997560 := by
    simpa [prefixWord, tailWord_997560, baseEnd_997560] using wordTrace_append hprefix tailTrace_997560
  have hstable : (prefixWord ++ tailWord_997560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997560).length < 2 ^ (prefixWord ++ tailWord_997560).sum := by decide
  have hdescent : baseEnd_997560 < baseStart_997560 := by decide
  rcases family_descends (prefixWord ++ tailWord_997560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997563 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 3]
def baseStart_997563 : Nat := 118140960795 + 997563 * 2 ^ 59
def prefixEnd_997563 : Nat := 4983230072969 + 3 ^ 40 * 997563 * 2
def baseEnd_997563 : Nat := 512229302141185763874797

theorem tailTrace_997563 : CollatzResearch.WordTrace tailWord_997563 prefixEnd_997563 512229302141185763874797 := by
  unfold tailWord_997563
  simp only [CollatzResearch.WordTrace]
  refine ⟨36384111685007096041645343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24256074456671397361096895 36384111685007096041645343)
  ·
    refine ⟨54576167527510644062468015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36384111685007096041645343 54576167527510644062468015)
    ·
      refine ⟨81864251291265966093702023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54576167527510644062468015 81864251291265966093702023)
      ·
        refine ⟨122796376936898949140553035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81864251291265966093702023 122796376936898949140553035)
        ·
          refine ⟨184194565405348423710829553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122796376936898949140553035 184194565405348423710829553)
          ·
            refine ⟨138145924054011317783122165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184194565405348423710829553 138145924054011317783122165)
            ·
              refine ⟨12951180380063561042167703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138145924054011317783122165 12951180380063561042167703)
              ·
                refine ⟨19426770570095341563251555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12951180380063561042167703 19426770570095341563251555)
                ·
                  refine ⟨29140155855143012344877333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19426770570095341563251555 29140155855143012344877333)
                  ·
                    refine ⟨1365944805709828703666125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29140155855143012344877333 1365944805709828703666125)
                    ·
                      refine ⟨512229302141185763874797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1365944805709828703666125 512229302141185763874797)
                      ·
                        rfl

theorem cell23_997563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 3].length) (baseStart_997563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997563 prefixEnd_997563 := by exact prefixLift 997563
  have htrace : WordTrace (prefixWord ++ tailWord_997563) baseStart_997563 baseEnd_997563 := by
    simpa [prefixWord, tailWord_997563, baseEnd_997563] using wordTrace_append hprefix tailTrace_997563
  have hstable : (prefixWord ++ tailWord_997563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997563).length < 2 ^ (prefixWord ++ tailWord_997563).sum := by decide
  have hdescent : baseEnd_997563 < baseStart_997563 := by decide
  rcases family_descends (prefixWord ++ tailWord_997563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997573 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_997573 : Nat := 118140960795 + 997573 * 2 ^ 59
def prefixEnd_997573 : Nat := 4983230072969 + 3 ^ 40 * 997573 * 2
def baseEnd_997573 : Nat := 512234436947730724749751

theorem tailTrace_997573 : CollatzResearch.WordTrace tailWord_997573 prefixEnd_997573 512234436947730724749751 := by
  unfold tailWord_997573
  simp only [CollatzResearch.WordTrace]
  refine ⟨36384476414970867749509373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24256317609980578499672915 36384476414970867749509373)
  ·
    refine ⟨13644178655614075406066015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36384476414970867749509373 13644178655614075406066015)
    ·
      refine ⟨20466267983421113109099023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13644178655614075406066015 20466267983421113109099023)
      ·
        refine ⟨30699401975131669663648535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20466267983421113109099023 30699401975131669663648535)
        ·
          refine ⟨46049102962697504495472803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30699401975131669663648535 46049102962697504495472803)
          ·
            refine ⟨69073654444046256743209205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46049102962697504495472803 69073654444046256743209205)
            ·
              refine ⟨6475655104129336569675863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69073654444046256743209205 6475655104129336569675863)
              ·
                refine ⟨9713482656194004854513795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6475655104129336569675863 9713482656194004854513795)
                ·
                  refine ⟨14570223984291007281770693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9713482656194004854513795 14570223984291007281770693)
                  ·
                    refine ⟨2731916997054563865332005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14570223984291007281770693 2731916997054563865332005)
                    ·
                      refine ⟨512234436947730724749751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2731916997054563865332005 512234436947730724749751)
                      ·
                        rfl

theorem cell23_997573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_997573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997573 prefixEnd_997573 := by exact prefixLift 997573
  have htrace : WordTrace (prefixWord ++ tailWord_997573) baseStart_997573 baseEnd_997573 := by
    simpa [prefixWord, tailWord_997573, baseEnd_997573] using wordTrace_append hprefix tailTrace_997573
  have hstable : (prefixWord ++ tailWord_997573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997573).length < 2 ^ (prefixWord ++ tailWord_997573).sum := by decide
  have hdescent : baseEnd_997573 < baseStart_997573 := by decide
  rcases family_descends (prefixWord ++ tailWord_997573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997583 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 7]
def baseStart_997583 : Nat := 118140960795 + 997583 * 2 ^ 59
def prefixEnd_997583 : Nat := 4983230072969 + 3 ^ 40 * 997583 * 2
def baseEnd_997583 : Nat := 56915507972697298402745

theorem tailTrace_997583 : CollatzResearch.WordTrace tailWord_997583 prefixEnd_997583 56915507972697298402745 := by
  unfold tailWord_997583
  simp only [CollatzResearch.WordTrace]
  refine ⟨36384841144934639457373403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24256560763289759638248935 36384841144934639457373403)
  ·
    refine ⟨54577261717401959186060105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36384841144934639457373403 54577261717401959186060105)
    ·
      refine ⟨40932946288051469389545079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54577261717401959186060105 40932946288051469389545079)
      ·
        refine ⟨61399419432077204084317619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40932946288051469389545079 61399419432077204084317619)
        ·
          refine ⟨92099129148115806126476429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61399419432077204084317619 92099129148115806126476429)
          ·
            refine ⟨34537173430543427297428661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92099129148115806126476429 34537173430543427297428661)
            ·
              refine ⟨3237860009113446309133937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34537173430543427297428661 3237860009113446309133937)
              ·
                refine ⟨2428395006835084731850453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3237860009113446309133937 2428395006835084731850453)
                ·
                  refine ⟨56915507972697298402745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2428395006835084731850453 56915507972697298402745)
                  ·
                    rfl

theorem cell23_997583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 7].length) (baseStart_997583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997583 prefixEnd_997583 := by exact prefixLift 997583
  have htrace : WordTrace (prefixWord ++ tailWord_997583) baseStart_997583 baseEnd_997583 := by
    simpa [prefixWord, tailWord_997583, baseEnd_997583] using wordTrace_append hprefix tailTrace_997583
  have hstable : (prefixWord ++ tailWord_997583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997583).length < 2 ^ (prefixWord ++ tailWord_997583).sum := by decide
  have hdescent : baseEnd_997583 < baseStart_997583 := by decide
  rcases family_descends (prefixWord ++ tailWord_997583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997610 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_997610 : Nat := 118140960795 + 997610 * 2 ^ 59
def prefixEnd_997610 : Nat := 4983230072969 + 3 ^ 40 * 997610 * 2
def baseEnd_997610 : Nat := 512253435731947079987081

theorem tailTrace_997610 : CollatzResearch.WordTrace tailWord_997610 prefixEnd_997610 512253435731947079987081 := by
  unfold tailWord_997610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096456478959205767151571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24257217277224548712404189 9096456478959205767151571)
  ·
    refine ⟨13644684718438808650727357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9096456478959205767151571 13644684718438808650727357)
    ·
      refine ⟨5116756769414553244022759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13644684718438808650727357 5116756769414553244022759)
      ·
        refine ⟨7675135154121829866034139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116756769414553244022759 7675135154121829866034139)
        ·
          refine ⟨11512702731182744799051209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7675135154121829866034139 11512702731182744799051209)
          ·
            refine ⟨8634527048387058599288407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11512702731182744799051209 8634527048387058599288407)
            ·
              refine ⟨12951790572580587898932611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634527048387058599288407 12951790572580587898932611)
              ·
                refine ⟨19427685858870881848398917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12951790572580587898932611 19427685858870881848398917)
                ·
                  refine ⟨3642691098538290346574797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19427685858870881848398917 3642691098538290346574797)
                  ·
                    refine ⟨1366009161951858879965549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3642691098538290346574797 1366009161951858879965549)
                    ·
                      refine ⟨512253435731947079987081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1366009161951858879965549 512253435731947079987081)
                      ·
                        rfl

theorem cell23_997610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_997610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997610 prefixEnd_997610 := by exact prefixLift 997610
  have htrace : WordTrace (prefixWord ++ tailWord_997610) baseStart_997610 baseEnd_997610 := by
    simpa [prefixWord, tailWord_997610, baseEnd_997610] using wordTrace_append hprefix tailTrace_997610
  have hstable : (prefixWord ++ tailWord_997610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997610).length < 2 ^ (prefixWord ++ tailWord_997610).sum := by decide
  have hdescent : baseEnd_997610 < baseStart_997610 := by decide
  rcases family_descends (prefixWord ++ tailWord_997610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997630 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_997630 : Nat := 118140960795 + 997630 * 2 ^ 59
def prefixEnd_997630 : Nat := 4983230072969 + 3 ^ 40 * 997630 * 2
def baseEnd_997630 : Nat := 170754568448345667245663

theorem tailTrace_997630 : CollatzResearch.WordTrace tailWord_997630 prefixEnd_997630 170754568448345667245663 := by
  unfold tailWord_997630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4548319421970545810541793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24257703583842910989556229 4548319421970545810541793)
  ·
    refine ⟨3411239566477909357906345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4548319421970545810541793 3411239566477909357906345)
    ·
      refine ⟨2558429674858432018429759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3411239566477909357906345 2558429674858432018429759)
      ·
        refine ⟨3837644512287648027644639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558429674858432018429759 3837644512287648027644639)
        ·
          refine ⟨5756466768431472041466959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837644512287648027644639 5756466768431472041466959)
          ·
            refine ⟨8634700152647208062200439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5756466768431472041466959 8634700152647208062200439)
            ·
              refine ⟨12952050228970812093300659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634700152647208062200439 12952050228970812093300659)
              ·
                refine ⟨19428075343456218139950989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12952050228970812093300659 19428075343456218139950989)
                ·
                  refine ⟨7285528253796081802481621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19428075343456218139950989 7285528253796081802481621)
                  ·
                    refine ⟨170754568448345667245663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7285528253796081802481621 170754568448345667245663)
                    ·
                      rfl

theorem cell23_997630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_997630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997630 prefixEnd_997630 := by exact prefixLift 997630
  have htrace : WordTrace (prefixWord ++ tailWord_997630) baseStart_997630 baseEnd_997630 := by
    simpa [prefixWord, tailWord_997630, baseEnd_997630] using wordTrace_append hprefix tailTrace_997630
  have hstable : (prefixWord ++ tailWord_997630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997630).length < 2 ^ (prefixWord ++ tailWord_997630).sum := by decide
  have hdescent : baseEnd_997630 < baseStart_997630 := by decide
  rcases family_descends (prefixWord ++ tailWord_997630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997643 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 2, 8]
def baseStart_997643 : Nat := 118140960795 + 997643 * 2 ^ 59
def prefixEnd_997643 : Nat := 4983230072969 + 3 ^ 40 * 997643 * 2
def baseEnd_997643 : Nat := 170756793531181816958143

theorem tailTrace_997643 : CollatzResearch.WordTrace tailWord_997643 prefixEnd_997643 170756793531181816958143 := by
  unfold tailWord_997643
  simp only [CollatzResearch.WordTrace]
  refine ⟨36387029524717269704557583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24258019683144846469705055 36387029524717269704557583)
  ·
    refine ⟨54580544287075904556836375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36387029524717269704557583 54580544287075904556836375)
    ·
      refine ⟨81870816430613856835254563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54580544287075904556836375 81870816430613856835254563)
      ·
        refine ⟨122806224645920785252881845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81870816430613856835254563 122806224645920785252881845)
        ·
          refine ⟨11513083560555073617457673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122806224645920785252881845 11513083560555073617457673)
          ·
            refine ⟨8634812670416305213093255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11513083560555073617457673 8634812670416305213093255)
            ·
              refine ⟨12952219005624457819639883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634812670416305213093255 12952219005624457819639883)
              ·
                refine ⟨19428328508436686729459825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12952219005624457819639883 19428328508436686729459825)
                ·
                  refine ⟨14571246381327515047094869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19428328508436686729459825 14571246381327515047094869)
                  ·
                    refine ⟨170756793531181816958143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14571246381327515047094869 170756793531181816958143)
                    ·
                      rfl

theorem cell23_997643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 8].length) (baseStart_997643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997643 prefixEnd_997643 := by exact prefixLift 997643
  have htrace : WordTrace (prefixWord ++ tailWord_997643) baseStart_997643 baseEnd_997643 := by
    simpa [prefixWord, tailWord_997643, baseEnd_997643] using wordTrace_append hprefix tailTrace_997643
  have hstable : (prefixWord ++ tailWord_997643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997643).length < 2 ^ (prefixWord ++ tailWord_997643).sum := by decide
  have hdescent : baseEnd_997643 < baseStart_997643 := by decide
  rcases family_descends (prefixWord ++ tailWord_997643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997728 : List Nat := [2, 1, 1, 3, 5, 2, 2, 2, 1, 4]
def baseStart_997728 : Nat := 118140960795 + 997728 * 2 ^ 59
def prefixEnd_997728 : Nat := 4983230072969 + 3 ^ 40 * 997728 * 2
def baseEnd_997728 : Nat := 170771342149725872770513

theorem tailTrace_997728 : CollatzResearch.WordTrace tailWord_997728 prefixEnd_997728 170771342149725872770513 := by
  unfold tailWord_997728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18195064864704664610700919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24260086486272886147601225 18195064864704664610700919)
  ·
    refine ⟨27292597297056996916051379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18195064864704664610700919 27292597297056996916051379)
    ·
      refine ⟨40938895945585495374077069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27292597297056996916051379 40938895945585495374077069)
      ·
        refine ⟨15352085979594560765278901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40938895945585495374077069 15352085979594560765278901)
        ·
          refine ⟨1439258060586990071744897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15352085979594560765278901 1439258060586990071744897)
          ·
            refine ⟨1079443545440242553808673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439258060586990071744897 1079443545440242553808673)
            ·
              refine ⟨809582659080181915356505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079443545440242553808673 809582659080181915356505)
              ·
                refine ⟨607186994310136436517379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809582659080181915356505 607186994310136436517379)
                ·
                  refine ⟨910780491465204654776069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 607186994310136436517379 910780491465204654776069)
                  ·
                    refine ⟨170771342149725872770513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 910780491465204654776069 170771342149725872770513)
                    ·
                      rfl

theorem cell23_997728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 4].length) (baseStart_997728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997728 prefixEnd_997728 := by exact prefixLift 997728
  have htrace : WordTrace (prefixWord ++ tailWord_997728) baseStart_997728 baseEnd_997728 := by
    simpa [prefixWord, tailWord_997728, baseEnd_997728] using wordTrace_append hprefix tailTrace_997728
  have hstable : (prefixWord ++ tailWord_997728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997728).length < 2 ^ (prefixWord ++ tailWord_997728).sum := by decide
  have hdescent : baseEnd_997728 < baseStart_997728 := by decide
  rcases family_descends (prefixWord ++ tailWord_997728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997757 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_997757 : Nat := 118140960795 + 997757 * 2 ^ 59
def prefixEnd_997757 : Nat := 4983230072969 + 3 ^ 40 * 997757 * 2
def baseEnd_997757 : Nat := 512328917388158004848905

theorem tailTrace_997757 : CollatzResearch.WordTrace tailWord_997757 prefixEnd_997757 512328917388158004848905 := by
  unfold tailWord_997757
  simp only [CollatzResearch.WordTrace]
  refine ⟨36391187446304267174207525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24260791630869511449471683 36391187446304267174207525)
  ·
    refine ⟨6823347646182050095163911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36391187446304267174207525 6823347646182050095163911)
    ·
      refine ⟨10235021469273075142745867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6823347646182050095163911 10235021469273075142745867)
      ·
        refine ⟨15352532203909612714118801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10235021469273075142745867 15352532203909612714118801)
        ·
          refine ⟨11514399152932209535589101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15352532203909612714118801 11514399152932209535589101)
          ·
            refine ⟨4317899682349578575845913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11514399152932209535589101 4317899682349578575845913)
            ·
              refine ⟨3238424761762183931884435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4317899682349578575845913 3238424761762183931884435)
              ·
                refine ⟨4857637142643275897826653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238424761762183931884435 4857637142643275897826653)
                ·
                  refine ⟨1821613928491228461684995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4857637142643275897826653 1821613928491228461684995)
                  ·
                    refine ⟨2732420892736842692527493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821613928491228461684995 2732420892736842692527493)
                    ·
                      refine ⟨512328917388158004848905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2732420892736842692527493 512328917388158004848905)
                      ·
                        rfl

theorem cell23_997757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_997757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997757 prefixEnd_997757 := by exact prefixLift 997757
  have htrace : WordTrace (prefixWord ++ tailWord_997757) baseStart_997757 baseEnd_997757 := by
    simpa [prefixWord, tailWord_997757, baseEnd_997757] using wordTrace_append hprefix tailTrace_997757
  have hstable : (prefixWord ++ tailWord_997757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997757).length < 2 ^ (prefixWord ++ tailWord_997757).sum := by decide
  have hdescent : baseEnd_997757 < baseStart_997757 := by decide
  rcases family_descends (prefixWord ++ tailWord_997757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997761 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_997761 : Nat := 118140960795 + 997761 * 2 ^ 59
def prefixEnd_997761 : Nat := 4983230072969 + 3 ^ 40 * 997761 * 2
def baseEnd_997761 : Nat := 512330971310775989198887

theorem tailTrace_997761 : CollatzResearch.WordTrace tailWord_997761 prefixEnd_997761 512330971310775989198887 := by
  unfold tailWord_997761
  simp only [CollatzResearch.WordTrace]
  refine ⟨36391333338289775857353137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24260888892193183904902091 36391333338289775857353137)
  ·
    refine ⟨27293500003717331893014853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36391333338289775857353137 27293500003717331893014853)
    ·
      refine ⟨5117531250696999729940285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27293500003717331893014853 5117531250696999729940285)
      ·
        refine ⟨1919074219011374898727607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5117531250696999729940285 1919074219011374898727607)
        ·
          refine ⟨2878611328517062348091411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919074219011374898727607 2878611328517062348091411)
          ·
            refine ⟨4317916992775593522137117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878611328517062348091411 4317916992775593522137117)
            ·
              refine ⟨1619218872290847570801419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4317916992775593522137117 1619218872290847570801419)
              ·
                refine ⟨2428828308436271356202129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619218872290847570801419 2428828308436271356202129)
                ·
                  refine ⟨1821621231327203517151597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2428828308436271356202129 1821621231327203517151597)
                  ·
                    refine ⟨683107961747701318931849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1821621231327203517151597 683107961747701318931849)
                    ·
                      refine ⟨512330971310775989198887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 683107961747701318931849 512330971310775989198887)
                      ·
                        rfl

theorem cell23_997761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_997761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997761 prefixEnd_997761 := by exact prefixLift 997761
  have htrace : WordTrace (prefixWord ++ tailWord_997761) baseStart_997761 baseEnd_997761 := by
    simpa [prefixWord, tailWord_997761, baseEnd_997761] using wordTrace_append hprefix tailTrace_997761
  have hstable : (prefixWord ++ tailWord_997761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997761).length < 2 ^ (prefixWord ++ tailWord_997761).sum := by decide
  have hdescent : baseEnd_997761 < baseStart_997761 := by decide
  rcases family_descends (prefixWord ++ tailWord_997761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997767 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 4, 4]
def baseStart_997767 : Nat := 118140960795 + 997767 * 2 ^ 59
def prefixEnd_997767 : Nat := 4983230072969 + 3 ^ 40 * 997767 * 2
def baseEnd_997767 : Nat := 170778017398234321907953

theorem tailTrace_997767 : CollatzResearch.WordTrace tailWord_997767 prefixEnd_997767 170778017398234321907953 := by
  unfold tailWord_997767
  simp only [CollatzResearch.WordTrace]
  refine ⟨36391552176268038882071555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24261034784178692588047703 36391552176268038882071555)
  ·
    refine ⟨54587328264402058323107333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36391552176268038882071555 54587328264402058323107333)
    ·
      refine ⟨10235124049575385935582625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54587328264402058323107333 10235124049575385935582625)
      ·
        refine ⟨7676343037181539451686969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10235124049575385935582625 7676343037181539451686969)
        ·
          refine ⟨5757257277886154588765227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7676343037181539451686969 5757257277886154588765227)
          ·
            refine ⟨8635885916829231883147841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757257277886154588765227 8635885916829231883147841)
            ·
              refine ⟨6476914437621923912360881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8635885916829231883147841 6476914437621923912360881)
              ·
                refine ⟨4857685828216442934270661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476914437621923912360881 4857685828216442934270661)
                ·
                  refine ⟨910816092790583050175749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4857685828216442934270661 910816092790583050175749)
                  ·
                    refine ⟨170778017398234321907953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 910816092790583050175749 170778017398234321907953)
                    ·
                      rfl

theorem cell23_997767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_997767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997767 prefixEnd_997767 := by exact prefixLift 997767
  have htrace : WordTrace (prefixWord ++ tailWord_997767) baseStart_997767 baseEnd_997767 := by
    simpa [prefixWord, tailWord_997767, baseEnd_997767] using wordTrace_append hprefix tailTrace_997767
  have hstable : (prefixWord ++ tailWord_997767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997767).length < 2 ^ (prefixWord ++ tailWord_997767).sum := by decide
  have hdescent : baseEnd_997767 < baseStart_997767 := by decide
  rcases family_descends (prefixWord ++ tailWord_997767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997784 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 4, 4]
def baseStart_997784 : Nat := 118140960795 + 997784 * 2 ^ 59
def prefixEnd_997784 : Nat := 4983230072969 + 3 ^ 40 * 997784 * 2
def baseEnd_997784 : Nat := 170780927121943133070427

theorem tailTrace_997784 : CollatzResearch.WordTrace tailWord_997784 prefixEnd_997784 170780927121943133070427 := by
  unfold tailWord_997784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18196086108603225392720203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24261448144804300523626937 18196086108603225392720203)
  ·
    refine ⟨27294129162904838089080305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18196086108603225392720203 27294129162904838089080305)
    ·
      refine ⟨20470596872178628566810229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27294129162904838089080305 20470596872178628566810229)
      ·
        refine ⟨1919118456766746428138459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20470596872178628566810229 1919118456766746428138459)
        ·
          refine ⟨2878677685150119642207689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919118456766746428138459 2878677685150119642207689)
          ·
            refine ⟨2159008263862589731655767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2878677685150119642207689 2159008263862589731655767)
            ·
              refine ⟨3238512395793884597483651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159008263862589731655767 3238512395793884597483651)
              ·
                refine ⟨4857768593690826896225477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238512395793884597483651 4857768593690826896225477)
                ·
                  refine ⟨910831611317030043042277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4857768593690826896225477 910831611317030043042277)
                  ·
                    refine ⟨170780927121943133070427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 910831611317030043042277 170780927121943133070427)
                    ·
                      rfl

theorem cell23_997784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_997784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997784 prefixEnd_997784 := by exact prefixLift 997784
  have htrace : WordTrace (prefixWord ++ tailWord_997784) baseStart_997784 baseEnd_997784 := by
    simpa [prefixWord, tailWord_997784, baseEnd_997784] using wordTrace_append hprefix tailTrace_997784
  have hstable : (prefixWord ++ tailWord_997784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997784).length < 2 ^ (prefixWord ++ tailWord_997784).sum := by decide
  have hdescent : baseEnd_997784 < baseStart_997784 := by decide
  rcases family_descends (prefixWord ++ tailWord_997784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997791 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 3, 2, 2]
def baseStart_997791 : Nat := 118140960795 + 997791 * 2 ^ 59
def prefixEnd_997791 : Nat := 4983230072969 + 3 ^ 40 * 997791 * 2
def baseEnd_997791 : Nat := 512346375730410871823749

theorem tailTrace_997791 : CollatzResearch.WordTrace tailWord_997791 prefixEnd_997791 512346375730410871823749 := by
  unfold tailWord_997791
  simp only [CollatzResearch.WordTrace]
  refine ⟨36392427528181090980945227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24261618352120727320630151 36392427528181090980945227)
  ·
    refine ⟨54588641292271636471417841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36392427528181090980945227 54588641292271636471417841)
    ·
      refine ⟨40941480969203727353563381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54588641292271636471417841 40941480969203727353563381)
      ·
        refine ⟨3838263840862849439396567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40941480969203727353563381 3838263840862849439396567)
        ·
          refine ⟨5757395761294274159094851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3838263840862849439396567 5757395761294274159094851)
          ·
            refine ⟨8636093641941411238642277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757395761294274159094851 8636093641941411238642277)
            ·
              refine ⟨1619267557864014607245427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8636093641941411238642277 1619267557864014607245427)
              ·
                refine ⟨2428901336796021910868141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619267557864014607245427 2428901336796021910868141)
                ·
                  refine ⟨910838001298508216575553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2428901336796021910868141 910838001298508216575553)
                  ·
                    refine ⟨683128500973881162431665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 910838001298508216575553 683128500973881162431665)
                    ·
                      refine ⟨512346375730410871823749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 683128500973881162431665 512346375730410871823749)
                      ·
                        rfl

theorem cell23_997791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_997791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997791 prefixEnd_997791 := by exact prefixLift 997791
  have htrace : WordTrace (prefixWord ++ tailWord_997791) baseStart_997791 baseEnd_997791 := by
    simpa [prefixWord, tailWord_997791, baseEnd_997791] using wordTrace_append hprefix tailTrace_997791
  have hstable : (prefixWord ++ tailWord_997791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997791).length < 2 ^ (prefixWord ++ tailWord_997791).sum := by decide
  have hdescent : baseEnd_997791 < baseStart_997791 := by decide
  rcases family_descends (prefixWord ++ tailWord_997791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997842 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_997842 : Nat := 118140960795 + 997842 * 2 ^ 59
def prefixEnd_997842 : Nat := 4983230072969 + 3 ^ 40 * 997842 * 2
def baseEnd_997842 : Nat := 512372563243790172286015

theorem tailTrace_997842 : CollatzResearch.WordTrace tailWord_997842 prefixEnd_997842 512372563243790172286015 := by
  unfold tailWord_997842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9098571912749081672762945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24262858433997551127367853 9098571912749081672762945)
  ·
    refine ⟨6823928934561811254572209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9098571912749081672762945 6823928934561811254572209)
    ·
      refine ⟨5117946700921358440929157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6823928934561811254572209 5117946700921358440929157)
      ·
        refine ⟨959615006422754707674217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5117946700921358440929157 959615006422754707674217)
        ·
          refine ⟨719711254817066030755663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959615006422754707674217 719711254817066030755663)
          ·
            refine ⟨1079566882225599046133495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719711254817066030755663 1079566882225599046133495)
            ·
              refine ⟨1619350323338398569200243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079566882225599046133495 1619350323338398569200243)
              ·
                refine ⟨2429025485007597853800365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619350323338398569200243 2429025485007597853800365)
                ·
                  refine ⟨910884556877849195175137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2429025485007597853800365 910884556877849195175137)
                  ·
                    refine ⟨683163417658386896381353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 910884556877849195175137 683163417658386896381353)
                    ·
                      refine ⟨512372563243790172286015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 683163417658386896381353 512372563243790172286015)
                      ·
                        rfl

theorem cell23_997842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_997842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997842 prefixEnd_997842 := by exact prefixLift 997842
  have htrace : WordTrace (prefixWord ++ tailWord_997842) baseStart_997842 baseEnd_997842 := by
    simpa [prefixWord, tailWord_997842, baseEnd_997842] using wordTrace_append hprefix tailTrace_997842
  have hstable : (prefixWord ++ tailWord_997842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997842).length < 2 ^ (prefixWord ++ tailWord_997842).sum := by decide
  have hdescent : baseEnd_997842 < baseStart_997842 := by decide
  rcases family_descends (prefixWord ++ tailWord_997842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997898 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_997898 : Nat := 118140960795 + 997898 * 2 ^ 59
def prefixEnd_997898 : Nat := 4983230072969 + 3 ^ 40 * 997898 * 2
def baseEnd_997898 : Nat := 512401318160441953185757

theorem tailTrace_997898 : CollatzResearch.WordTrace tailWord_997898 prefixEnd_997898 512401318160441953185757 := by
  unfold tailWord_997898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099082534698362063772587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24264220092528965503393565 9099082534698362063772587)
  ·
    refine ⟨13648623802047543095658881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9099082534698362063772587 13648623802047543095658881)
    ·
      refine ⟨10236467851535657321744161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13648623802047543095658881 10236467851535657321744161)
      ·
        refine ⟨7677350888651742991308121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10236467851535657321744161 7677350888651742991308121)
        ·
          refine ⟨5758013166488807243481091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7677350888651742991308121 5758013166488807243481091)
          ·
            refine ⟨8637019749733210865221637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758013166488807243481091 8637019749733210865221637)
            ·
              refine ⟨1619441203074977037229057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8637019749733210865221637 1619441203074977037229057)
              ·
                refine ⟨1214580902306232777921793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1619441203074977037229057 1214580902306232777921793)
                ·
                  refine ⟨910935676729674583441345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1214580902306232777921793 910935676729674583441345)
                  ·
                    refine ⟨683201757547255937581009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 910935676729674583441345 683201757547255937581009)
                    ·
                      refine ⟨512401318160441953185757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 683201757547255937581009 512401318160441953185757)
                      ·
                        rfl

theorem cell23_997898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_997898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997898 prefixEnd_997898 := by exact prefixLift 997898
  have htrace : WordTrace (prefixWord ++ tailWord_997898) baseStart_997898 baseEnd_997898 := by
    simpa [prefixWord, tailWord_997898, baseEnd_997898] using wordTrace_append hprefix tailTrace_997898
  have hstable : (prefixWord ++ tailWord_997898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997898).length < 2 ^ (prefixWord ++ tailWord_997898).sum := by decide
  have hdescent : baseEnd_997898 < baseStart_997898 := by decide
  rcases family_descends (prefixWord ++ tailWord_997898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997911 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 4]
def baseStart_997911 : Nat := 118140960795 + 997911 * 2 ^ 59
def prefixEnd_997911 : Nat := 4983230072969 + 3 ^ 40 * 997911 * 2
def baseEnd_997911 : Nat := 512407993408950402323197

theorem tailTrace_997911 : CollatzResearch.WordTrace tailWord_997911 prefixEnd_997911 512407993408950402323197 := by
  unfold tailWord_997911
  simp only [CollatzResearch.WordTrace]
  refine ⟨36396804287746351475313587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24264536191830900983542391 36396804287746351475313587)
  ·
    refine ⟨54595206431619527212970381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36396804287746351475313587 54595206431619527212970381)
    ·
      refine ⟨20473202411857322704863893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54595206431619527212970381 20473202411857322704863893)
      ·
        refine ⟨959681363055812001790495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20473202411857322704863893 959681363055812001790495)
        ·
          refine ⟨1439522044583718002685743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959681363055812001790495 1439522044583718002685743)
          ·
            refine ⟨2159283066875577004028615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439522044583718002685743 2159283066875577004028615)
            ·
              refine ⟨3238924600313365506042923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159283066875577004028615 3238924600313365506042923)
              ·
                refine ⟨4858386900470048259064385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238924600313365506042923 4858386900470048259064385)
                ·
                  refine ⟨3643790175352536194298289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4858386900470048259064385 3643790175352536194298289)
                  ·
                    refine ⟨2732842631514402145723717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3643790175352536194298289 2732842631514402145723717)
                    ·
                      refine ⟨512407993408950402323197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2732842631514402145723717 512407993408950402323197)
                      ·
                        rfl

theorem cell23_997911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_997911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_997911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_997911 prefixEnd_997911 := by exact prefixLift 997911
  have htrace : WordTrace (prefixWord ++ tailWord_997911) baseStart_997911 baseEnd_997911 := by
    simpa [prefixWord, tailWord_997911, baseEnd_997911] using wordTrace_append hprefix tailTrace_997911
  have hstable : (prefixWord ++ tailWord_997911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997911).length < 2 ^ (prefixWord ++ tailWord_997911).sum := by decide
  have hdescent : baseEnd_997911 < baseStart_997911 := by decide
  rcases family_descends (prefixWord ++ tailWord_997911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998067 : List Nat := [1, 1, 1, 2, 3, 15]
def baseStart_998067 : Nat := 118140960795 + 998067 * 2 ^ 59
def prefixEnd_998067 : Nat := 4983230072969 + 3 ^ 40 * 998067 * 2
def baseEnd_998067 : Nat := 2109004511897332477253

theorem tailTrace_998067 : CollatzResearch.WordTrace tailWord_998067 prefixEnd_998067 2109004511897332477253 := by
  unfold tailWord_998067
  simp only [CollatzResearch.WordTrace]
  refine ⟨36402494075181190117992455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24268329383454126745328303 36402494075181190117992455)
  ·
    refine ⟨54603741112771785176988683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36402494075181190117992455 54603741112771785176988683)
    ·
      refine ⟨81905611669157677765483025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54603741112771785176988683 81905611669157677765483025)
      ·
        refine ⟨61429208751868258324112269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81905611669157677765483025 61429208751868258324112269)
        ·
          refine ⟨23035953281950596871542101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61429208751868258324112269 23035953281950596871542101)
          ·
            refine ⟨2109004511897332477253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 23035953281950596871542101 2109004511897332477253)
            ·
              rfl

theorem cell23_998067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 15].length) (baseStart_998067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998067 prefixEnd_998067 := by exact prefixLift 998067
  have htrace : WordTrace (prefixWord ++ tailWord_998067) baseStart_998067 baseEnd_998067 := by
    simpa [prefixWord, tailWord_998067, baseEnd_998067] using wordTrace_append hprefix tailTrace_998067
  have hstable : (prefixWord ++ tailWord_998067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998067).length < 2 ^ (prefixWord ++ tailWord_998067).sum := by decide
  have hdescent : baseEnd_998067 < baseStart_998067 := by decide
  rcases family_descends (prefixWord ++ tailWord_998067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998074 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_998074 : Nat := 118140960795 + 998074 * 2 ^ 59
def prefixEnd_998074 : Nat := 4983230072969 + 3 ^ 40 * 998074 * 2
def baseEnd_998074 : Nat := 512491690755633264584947

theorem tailTrace_998074 : CollatzResearch.WordTrace tailWord_998074 prefixEnd_998074 512491690755633264584947 := by
  unfold tailWord_998074
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100687346538957578374319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24268499590770553542331517 9100687346538957578374319)
  ·
    refine ⟨13651031019808436367561479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100687346538957578374319 13651031019808436367561479)
    ·
      refine ⟨20476546529712654551342219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13651031019808436367561479 20476546529712654551342219)
      ·
        refine ⟨30714819794568981827013329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20476546529712654551342219 30714819794568981827013329)
        ·
          refine ⟨23036114845926736370259997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30714819794568981827013329 23036114845926736370259997)
          ·
            refine ⟨8638543067222526138847499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23036114845926736370259997 8638543067222526138847499)
            ·
              refine ⟨12957814600833789208271249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8638543067222526138847499 12957814600833789208271249)
              ·
                refine ⟨9718360950625341906203437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12957814600833789208271249 9718360950625341906203437)
                ·
                  refine ⟨3644385356484503214826289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9718360950625341906203437 3644385356484503214826289)
                  ·
                    refine ⟨2733289017363377411119717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3644385356484503214826289 2733289017363377411119717)
                    ·
                      refine ⟨512491690755633264584947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2733289017363377411119717 512491690755633264584947)
                      ·
                        rfl

theorem cell23_998074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_998074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998074 prefixEnd_998074 := by exact prefixLift 998074
  have htrace : WordTrace (prefixWord ++ tailWord_998074) baseStart_998074 baseEnd_998074 := by
    simpa [prefixWord, tailWord_998074, baseEnd_998074] using wordTrace_append hprefix tailTrace_998074
  have hstable : (prefixWord ++ tailWord_998074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998074).length < 2 ^ (prefixWord ++ tailWord_998074).sum := by decide
  have hdescent : baseEnd_998074 < baseStart_998074 := by decide
  rcases family_descends (prefixWord ++ tailWord_998074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998108 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_998108 : Nat := 118140960795 + 998108 * 2 ^ 59
def prefixEnd_998108 : Nat := 4983230072969 + 3 ^ 40 * 998108 * 2
def baseEnd_998108 : Nat := 512509149097886131559791

theorem tailTrace_998108 : CollatzResearch.WordTrace tailWord_998108 prefixEnd_998108 512509149097886131559791 := by
  unfold tailWord_998108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18201994734016327060117489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24269326312021769413489985 18201994734016327060117489)
  ·
    refine ⟨13651496050512245295088117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18201994734016327060117489 13651496050512245295088117)
    ·
      refine ⟨1279827754735522996414511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13651496050512245295088117 1279827754735522996414511)
      ·
        refine ⟨1919741632103284494621767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279827754735522996414511 1919741632103284494621767)
        ·
          refine ⟨2879612448154926741932651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919741632103284494621767 2879612448154926741932651)
          ·
            refine ⟨4319418672232390112898977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879612448154926741932651 4319418672232390112898977)
            ·
              refine ⟨3239564004174292584674233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4319418672232390112898977 3239564004174292584674233)
              ·
                refine ⟨2429673003130719438505675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239564004174292584674233 2429673003130719438505675)
                ·
                  refine ⟨3644509504696079157758513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429673003130719438505675 3644509504696079157758513)
                  ·
                    refine ⟨2733382128522059368318885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3644509504696079157758513 2733382128522059368318885)
                    ·
                      refine ⟨512509149097886131559791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2733382128522059368318885 512509149097886131559791)
                      ·
                        rfl

theorem cell23_998108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_998108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998108 prefixEnd_998108 := by exact prefixLift 998108
  have htrace : WordTrace (prefixWord ++ tailWord_998108) baseStart_998108 baseEnd_998108 := by
    simpa [prefixWord, tailWord_998108, baseEnd_998108] using wordTrace_append hprefix tailTrace_998108
  have hstable : (prefixWord ++ tailWord_998108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998108).length < 2 ^ (prefixWord ++ tailWord_998108).sum := by decide
  have hdescent : baseEnd_998108 < baseStart_998108 := by decide
  rcases family_descends (prefixWord ++ tailWord_998108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998111 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 3]
def baseStart_998111 : Nat := 118140960795 + 998111 * 2 ^ 59
def prefixEnd_998111 : Nat := 4983230072969 + 3 ^ 40 * 998111 * 2
def baseEnd_998111 : Nat := 512510689539849619822277

theorem tailTrace_998111 : CollatzResearch.WordTrace tailWord_998111 prefixEnd_998111 512510689539849619822277 := by
  unfold tailWord_998111
  simp only [CollatzResearch.WordTrace]
  refine ⟨36404098887021785632594187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24269399258014523755062791 36404098887021785632594187)
  ·
    refine ⟨54606148330532678448891281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36404098887021785632594187 54606148330532678448891281)
    ·
      refine ⟨40954611247899508836668461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54606148330532678448891281 40954611247899508836668461)
      ·
        refine ⟨15357979217962315813750673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40954611247899508836668461 15357979217962315813750673)
        ·
          refine ⟨11518484413471736860313005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15357979217962315813750673 11518484413471736860313005)
          ·
            refine ⟨4319431655051901322617377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11518484413471736860313005 4319431655051901322617377)
            ·
              refine ⟨3239573741288925991963033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4319431655051901322617377 3239573741288925991963033)
              ·
                refine ⟨2429680305966694493972275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239573741288925991963033 2429680305966694493972275)
                ·
                  refine ⟨3644520458950041740958413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429680305966694493972275 3644520458950041740958413)
                  ·
                    refine ⟨1366695172106265652859405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644520458950041740958413 1366695172106265652859405)
                    ·
                      refine ⟨512510689539849619822277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1366695172106265652859405 512510689539849619822277)
                      ·
                        rfl

theorem cell23_998111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_998111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998111 prefixEnd_998111 := by exact prefixLift 998111
  have htrace : WordTrace (prefixWord ++ tailWord_998111) baseStart_998111 baseEnd_998111 := by
    simpa [prefixWord, tailWord_998111, baseEnd_998111] using wordTrace_append hprefix tailTrace_998111
  have hstable : (prefixWord ++ tailWord_998111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998111).length < 2 ^ (prefixWord ++ tailWord_998111).sum := by decide
  have hdescent : baseEnd_998111 < baseStart_998111 := by decide
  rcases family_descends (prefixWord ++ tailWord_998111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998115 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 1, 2, 3]
def baseStart_998115 : Nat := 118140960795 + 998115 * 2 ^ 59
def prefixEnd_998115 : Nat := 4983230072969 + 3 ^ 40 * 998115 * 2
def baseEnd_998115 : Nat := 512512743462467604172259

theorem tailTrace_998115 : CollatzResearch.WordTrace tailWord_998115 prefixEnd_998115 512512743462467604172259 := by
  unfold tailWord_998115
  simp only [CollatzResearch.WordTrace]
  refine ⟨36404244779007294315739799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24269496519338196210493199 36404244779007294315739799)
  ·
    refine ⟨54606367168510941473609699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36404244779007294315739799 54606367168510941473609699)
    ·
      refine ⟨81909550752766412210414549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54606367168510941473609699 81909550752766412210414549)
      ·
        refine ⟨1919755095767962786181591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 81909550752766412210414549 1919755095767962786181591)
        ·
          refine ⟨2879632643651944179272387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919755095767962786181591 2879632643651944179272387)
          ·
            refine ⟨4319448965477916268908581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879632643651944179272387 4319448965477916268908581)
            ·
              refine ⟨809896681027109300420359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4319448965477916268908581 809896681027109300420359)
              ·
                refine ⟨1214845021540663950630539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809896681027109300420359 1214845021540663950630539)
                ·
                  refine ⟨1822267532310995925945809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214845021540663950630539 1822267532310995925945809)
                  ·
                    refine ⟨1366700649233246944459357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1822267532310995925945809 1366700649233246944459357)
                    ·
                      refine ⟨512512743462467604172259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1366700649233246944459357 512512743462467604172259)
                      ·
                        rfl

theorem cell23_998115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_998115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998115 prefixEnd_998115 := by exact prefixLift 998115
  have htrace : WordTrace (prefixWord ++ tailWord_998115) baseStart_998115 baseEnd_998115 := by
    simpa [prefixWord, tailWord_998115, baseEnd_998115] using wordTrace_append hprefix tailTrace_998115
  have hstable : (prefixWord ++ tailWord_998115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998115).length < 2 ^ (prefixWord ++ tailWord_998115).sum := by decide
  have hdescent : baseEnd_998115 < baseStart_998115 := by decide
  rcases family_descends (prefixWord ++ tailWord_998115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998196 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_998196 : Nat := 118140960795 + 998196 * 2 ^ 59
def prefixEnd_998196 : Nat := 4983230072969 + 3 ^ 40 * 998196 * 2
def baseEnd_998196 : Nat := 512554335395481787259387

theorem tailTrace_998196 : CollatzResearch.WordTrace tailWord_998196 prefixEnd_998196 512554335395481787259387 := by
  unfold tailWord_998196
  simp only [CollatzResearch.WordTrace]
  refine ⟨18203599545856922574719221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24271466061142563432958961 18203599545856922574719221)
  ·
    refine ⟨1706587457424086491379927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18203599545856922574719221 1706587457424086491379927)
    ·
      refine ⟨2559881186136129737069891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706587457424086491379927 2559881186136129737069891)
      ·
        refine ⟨3839821779204194605604837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559881186136129737069891 3839821779204194605604837)
        ·
          refine ⟨719966583600786488550907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3839821779204194605604837 719966583600786488550907)
          ·
            refine ⟨1079949875401179732826361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719966583600786488550907 1079949875401179732826361)
            ·
              refine ⟨809962406550884799619771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079949875401179732826361 809962406550884799619771)
              ·
                refine ⟨1214943609826327199429657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809962406550884799619771 1214943609826327199429657)
                ·
                  refine ⟨911207707369745399572243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1214943609826327199429657 911207707369745399572243)
                  ·
                    refine ⟨1366811561054618099358365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 911207707369745399572243 1366811561054618099358365)
                    ·
                      refine ⟨512554335395481787259387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1366811561054618099358365 512554335395481787259387)
                      ·
                        rfl

theorem cell23_998196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_998196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998196 prefixEnd_998196 := by exact prefixLift 998196
  have htrace : WordTrace (prefixWord ++ tailWord_998196) baseStart_998196 baseEnd_998196 := by
    simpa [prefixWord, tailWord_998196, baseEnd_998196] using wordTrace_append hprefix tailTrace_998196
  have hstable : (prefixWord ++ tailWord_998196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998196).length < 2 ^ (prefixWord ++ tailWord_998196).sum := by decide
  have hdescent : baseEnd_998196 < baseStart_998196 := by decide
  rcases family_descends (prefixWord ++ tailWord_998196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998202 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2]
def baseStart_998202 : Nat := 118140960795 + 998202 * 2 ^ 59
def prefixEnd_998202 : Nat := 4983230072969 + 3 ^ 40 * 998202 * 2
def baseEnd_998202 : Nat := 512557416279408763784359

theorem tailTrace_998202 : CollatzResearch.WordTrace tailWord_998202 prefixEnd_998202 512557416279408763784359 := by
  unfold tailWord_998202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9101854482423027043539215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24271611953128072116104573 9101854482423027043539215)
  ·
    refine ⟨13652781723634540565308823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9101854482423027043539215 13652781723634540565308823)
    ·
      refine ⟨20479172585451810847963235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13652781723634540565308823 20479172585451810847963235)
      ·
        refine ⟨30718758878177716271944853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20479172585451810847963235 30718758878177716271944853)
        ·
          refine ⟨1439941822414580450247415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30718758878177716271944853 1439941822414580450247415)
          ·
            refine ⟨2159912733621870675371123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439941822414580450247415 2159912733621870675371123)
            ·
              refine ⟨3239869100432806013056685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159912733621870675371123 3239869100432806013056685)
              ·
                refine ⟨1214950912662302254896257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3239869100432806013056685 1214950912662302254896257)
                ·
                  refine ⟨911213184496726691172193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1214950912662302254896257 911213184496726691172193)
                  ·
                    refine ⟨683409888372545018379145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 911213184496726691172193 683409888372545018379145)
                    ·
                      refine ⟨512557416279408763784359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 683409888372545018379145 512557416279408763784359)
                      ·
                        rfl

theorem cell23_998202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_998202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998202 prefixEnd_998202 := by exact prefixLift 998202
  have htrace : WordTrace (prefixWord ++ tailWord_998202) baseStart_998202 baseEnd_998202 := by
    simpa [prefixWord, tailWord_998202, baseEnd_998202] using wordTrace_append hprefix tailTrace_998202
  have hstable : (prefixWord ++ tailWord_998202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998202).length < 2 ^ (prefixWord ++ tailWord_998202).sum := by decide
  have hdescent : baseEnd_998202 < baseStart_998202 := by decide
  rcases family_descends (prefixWord ++ tailWord_998202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998231 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_998231 : Nat := 118140960795 + 998231 * 2 ^ 59
def prefixEnd_998231 : Nat := 4983230072969 + 3 ^ 40 * 998231 * 2
def baseEnd_998231 : Nat := 512572307218389150321725

theorem tailTrace_998231 : CollatzResearch.WordTrace tailWord_998231 prefixEnd_998231 512572307218389150321725 := by
  unfold tailWord_998231
  simp only [CollatzResearch.WordTrace]
  refine ⟨36408475646587046126962547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24272317097724697417975031 36408475646587046126962547)
  ·
    refine ⟨54612713469880569190443821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36408475646587046126962547 54612713469880569190443821)
    ·
      refine ⟨20479767551205213446416433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54612713469880569190443821 20479767551205213446416433)
      ·
        refine ⟨15359825663403910084812325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20479767551205213446416433 15359825663403910084812325)
        ·
          refine ⟨2879967311888233140902311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15359825663403910084812325 2879967311888233140902311)
          ·
            refine ⟨4319950967832349711353467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879967311888233140902311 4319950967832349711353467)
            ·
              refine ⟨6479926451748524567030201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4319950967832349711353467 6479926451748524567030201)
              ·
                refine ⟨4859944838811393425272651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6479926451748524567030201 4859944838811393425272651)
                ·
                  refine ⟨7289917258217090137908977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859944838811393425272651 7289917258217090137908977)
                  ·
                    refine ⟨5467437943662817603431733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7289917258217090137908977 5467437943662817603431733)
                    ·
                      refine ⟨512572307218389150321725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5467437943662817603431733 512572307218389150321725)
                      ·
                        rfl

theorem cell23_998231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_998231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998231 prefixEnd_998231 := by exact prefixLift 998231
  have htrace : WordTrace (prefixWord ++ tailWord_998231) baseStart_998231 baseEnd_998231 := by
    simpa [prefixWord, tailWord_998231, baseEnd_998231] using wordTrace_append hprefix tailTrace_998231
  have hstable : (prefixWord ++ tailWord_998231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998231).length < 2 ^ (prefixWord ++ tailWord_998231).sum := by decide
  have hdescent : baseEnd_998231 < baseStart_998231 := by decide
  rcases family_descends (prefixWord ++ tailWord_998231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998241 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_998241 : Nat := 118140960795 + 998241 * 2 ^ 59
def prefixEnd_998241 : Nat := 4983230072969 + 3 ^ 40 * 998241 * 2
def baseEnd_998241 : Nat := 512577442024934111196679

theorem tailTrace_998241 : CollatzResearch.WordTrace tailWord_998241 prefixEnd_998241 512577442024934111196679 := by
  unfold tailWord_998241
  simp only [CollatzResearch.WordTrace]
  refine ⟨36408840376550817834826577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24272560251033878556551051 36408840376550817834826577)
  ·
    refine ⟨27306630282413113376119933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36408840376550817834826577 27306630282413113376119933)
    ·
      refine ⟨10239986355904917516044975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27306630282413113376119933 10239986355904917516044975)
      ·
        refine ⟨15359979533857376274067463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10239986355904917516044975 15359979533857376274067463)
        ·
          refine ⟨23039969300786064411101195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15359979533857376274067463 23039969300786064411101195)
          ·
            refine ⟨34559953951179096616651793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23039969300786064411101195 34559953951179096616651793)
            ·
              refine ⟨25919965463384322462488845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34559953951179096616651793 25919965463384322462488845)
              ·
                refine ⟨9719987048769120923433317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25919965463384322462488845 9719987048769120923433317)
                ·
                  refine ⟨1822497571644210173143747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9719987048769120923433317 1822497571644210173143747)
                  ·
                    refine ⟨2733746357466315259715621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1822497571644210173143747 2733746357466315259715621)
                    ·
                      refine ⟨512577442024934111196679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2733746357466315259715621 512577442024934111196679)
                      ·
                        rfl

theorem cell23_998241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_998241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998241 prefixEnd_998241 := by exact prefixLift 998241
  have htrace : WordTrace (prefixWord ++ tailWord_998241) baseStart_998241 baseEnd_998241 := by
    simpa [prefixWord, tailWord_998241, baseEnd_998241] using wordTrace_append hprefix tailTrace_998241
  have hstable : (prefixWord ++ tailWord_998241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998241).length < 2 ^ (prefixWord ++ tailWord_998241).sum := by decide
  have hdescent : baseEnd_998241 < baseStart_998241 := by decide
  rcases family_descends (prefixWord ++ tailWord_998241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998258 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_998258 : Nat := 118140960795 + 998258 * 2 ^ 59
def prefixEnd_998258 : Nat := 4983230072969 + 3 ^ 40 * 998258 * 2
def baseEnd_998258 : Nat := 512586171196060544684101

theorem tailTrace_998258 : CollatzResearch.WordTrace tailWord_998258 prefixEnd_998258 512586171196060544684101 := by
  unfold tailWord_998258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9102365104372307434548857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24272973611659486492130285 9102365104372307434548857)
  ·
    refine ⟨6826773828279230575911643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9102365104372307434548857 6826773828279230575911643)
    ·
      refine ⟨10240160742418845863867465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826773828279230575911643 10240160742418845863867465)
      ·
        refine ⟨7680120556814134397900599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10240160742418845863867465 7680120556814134397900599)
        ·
          refine ⟨11520180835221201596850899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7680120556814134397900599 11520180835221201596850899)
          ·
            refine ⟨17280271252831802395276349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11520180835221201596850899 17280271252831802395276349)
            ·
              refine ⟨6480101719811925898228631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17280271252831802395276349 6480101719811925898228631)
              ·
                refine ⟨9720152579717888847342947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480101719811925898228631 9720152579717888847342947)
                ·
                  refine ⟨14580228869576833271014421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9720152579717888847342947 14580228869576833271014421)
                  ·
                    refine ⟨683448228261414059578801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14580228869576833271014421 683448228261414059578801)
                    ·
                      refine ⟨512586171196060544684101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 683448228261414059578801 512586171196060544684101)
                      ·
                        rfl

theorem cell23_998258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_998258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998258 prefixEnd_998258 := by exact prefixLift 998258
  have htrace : WordTrace (prefixWord ++ tailWord_998258) baseStart_998258 baseEnd_998258 := by
    simpa [prefixWord, tailWord_998258, baseEnd_998258] using wordTrace_append hprefix tailTrace_998258
  have hstable : (prefixWord ++ tailWord_998258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998258).length < 2 ^ (prefixWord ++ tailWord_998258).sum := by decide
  have hdescent : baseEnd_998258 < baseStart_998258 := by decide
  rcases family_descends (prefixWord ++ tailWord_998258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998298 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 8]
def baseStart_998298 : Nat := 118140960795 + 998298 * 2 ^ 59
def prefixEnd_998298 : Nat := 4983230072969 + 3 ^ 40 * 998298 * 2
def baseEnd_998298 : Nat := 56956301158026709798213

theorem tailTrace_998298 : CollatzResearch.WordTrace tailWord_998298 prefixEnd_998298 56956301158026709798213 := by
  unfold tailWord_998298
  simp only [CollatzResearch.WordTrace]
  refine ⟨9102729834336079142412887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24273946224896211046434365 9102729834336079142412887)
  ·
    refine ⟨13654094751504118713619331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9102729834336079142412887 13654094751504118713619331)
    ·
      refine ⟨20481142127256178070428997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13654094751504118713619331 20481142127256178070428997)
      ·
        refine ⟨3840214148860533388205437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20481142127256178070428997 3840214148860533388205437)
        ·
          refine ⟨1440080305822700020577039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3840214148860533388205437 1440080305822700020577039)
          ·
            refine ⟨2160120458734050030865559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440080305822700020577039 2160120458734050030865559)
            ·
              refine ⟨3240180688101075046298339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160120458734050030865559 3240180688101075046298339)
              ·
                refine ⟨4860271032151612569447509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240180688101075046298339 4860271032151612569447509)
                ·
                  refine ⟨56956301158026709798213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4860271032151612569447509 56956301158026709798213)
                  ·
                    rfl

theorem cell23_998298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_998298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998298 prefixEnd_998298 := by exact prefixLift 998298
  have htrace : WordTrace (prefixWord ++ tailWord_998298) baseStart_998298 baseEnd_998298 := by
    simpa [prefixWord, tailWord_998298, baseEnd_998298] using wordTrace_append hprefix tailTrace_998298
  have hstable : (prefixWord ++ tailWord_998298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998298).length < 2 ^ (prefixWord ++ tailWord_998298).sum := by decide
  have hdescent : baseEnd_998298 < baseStart_998298 := by decide
  rcases family_descends (prefixWord ++ tailWord_998298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998301 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_998301 : Nat := 118140960795 + 998301 * 2 ^ 59
def prefixEnd_998301 : Nat := 4983230072969 + 3 ^ 40 * 998301 * 2
def baseEnd_998301 : Nat := 512608250864203876446403

theorem tailTrace_998301 : CollatzResearch.WordTrace tailWord_998301 prefixEnd_998301 512608250864203876446403 := by
  unfold tailWord_998301
  simp only [CollatzResearch.WordTrace]
  refine ⟨36411028756333448082010757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24274019170888965388007171 36411028756333448082010757)
  ·
    refine ⟨6827067891812521515377017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36411028756333448082010757 6827067891812521515377017)
    ·
      refine ⟨5120300918859391136532763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6827067891812521515377017 5120300918859391136532763)
      ·
        refine ⟨7680451378289086704799145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5120300918859391136532763 7680451378289086704799145)
        ·
          refine ⟨5760338533716815028599359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7680451378289086704799145 5760338533716815028599359)
          ·
            refine ⟨8640507800575222542899039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760338533716815028599359 8640507800575222542899039)
            ·
              refine ⟨12960761700862833814348559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640507800575222542899039 12960761700862833814348559)
              ·
                refine ⟨19441142551294250721522839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12960761700862833814348559 19441142551294250721522839)
                ·
                  refine ⟨29161713826941376082284259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19441142551294250721522839 29161713826941376082284259)
                  ·
                    refine ⟨43742570740412064123426389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29161713826941376082284259 43742570740412064123426389)
                    ·
                      refine ⟨512608250864203876446403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 43742570740412064123426389 512608250864203876446403)
                      ·
                        rfl

theorem cell23_998301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_998301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998301 prefixEnd_998301 := by exact prefixLift 998301
  have htrace : WordTrace (prefixWord ++ tailWord_998301) baseStart_998301 baseEnd_998301 := by
    simpa [prefixWord, tailWord_998301, baseEnd_998301] using wordTrace_append hprefix tailTrace_998301
  have hstable : (prefixWord ++ tailWord_998301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998301).length < 2 ^ (prefixWord ++ tailWord_998301).sum := by decide
  have hdescent : baseEnd_998301 < baseStart_998301 := by decide
  rcases family_descends (prefixWord ++ tailWord_998301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998325 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_998325 : Nat := 118140960795 + 998325 * 2 ^ 59
def prefixEnd_998325 : Nat := 4983230072969 + 3 ^ 40 * 998325 * 2
def baseEnd_998325 : Nat := 512620574399911782546293

theorem tailTrace_998325 : CollatzResearch.WordTrace tailWord_998325 prefixEnd_998325 512620574399911782546293 := by
  unfold tailWord_998325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36411904108246500180884429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24274602738831000120589619 36411904108246500180884429)
  ·
    refine ⟨13654464040592437567831661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36411904108246500180884429 13654464040592437567831661)
    ·
      refine ⟨5120424015222164087936873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13654464040592437567831661 5120424015222164087936873)
      ·
        refine ⟨3840318011416623065952655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5120424015222164087936873 3840318011416623065952655)
        ·
          refine ⟨5760477017124934598928983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3840318011416623065952655 5760477017124934598928983)
          ·
            refine ⟨8640715525687401898393475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760477017124934598928983 8640715525687401898393475)
            ·
              refine ⟨12961073288531102847590213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640715525687401898393475 12961073288531102847590213)
              ·
                refine ⟨2430201241599581783923165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12961073288531102847590213 2430201241599581783923165)
                ·
                  refine ⟨911325465599843168971187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2430201241599581783923165 911325465599843168971187)
                  ·
                    refine ⟨1366988198399764753456781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 911325465599843168971187 1366988198399764753456781)
                    ·
                      refine ⟨512620574399911782546293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1366988198399764753456781 512620574399911782546293)
                      ·
                        rfl

theorem cell23_998325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_998325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998325 prefixEnd_998325 := by exact prefixLift 998325
  have htrace : WordTrace (prefixWord ++ tailWord_998325) baseStart_998325 baseEnd_998325 := by
    simpa [prefixWord, tailWord_998325, baseEnd_998325] using wordTrace_append hprefix tailTrace_998325
  have hstable : (prefixWord ++ tailWord_998325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998325).length < 2 ^ (prefixWord ++ tailWord_998325).sum := by decide
  have hdescent : baseEnd_998325 < baseStart_998325 := by decide
  rcases family_descends (prefixWord ++ tailWord_998325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998328 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 1, 5]
def baseStart_998328 : Nat := 118140960795 + 998328 * 2 ^ 59
def prefixEnd_998328 : Nat := 4983230072969 + 3 ^ 40 * 998328 * 2
def baseEnd_998328 : Nat := 170874038280625090269593

theorem tailTrace_998328 : CollatzResearch.WordTrace tailWord_998328 prefixEnd_998328 170874038280625090269593 := by
  unfold tailWord_998328
  simp only [CollatzResearch.WordTrace]
  refine ⟨18206006763617815846621819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24274675684823754462162425 18206006763617815846621819)
  ·
    refine ⟨27309010145426723769932729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18206006763617815846621819 27309010145426723769932729)
    ·
      refine ⟨20481757609070042827449547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27309010145426723769932729 20481757609070042827449547)
      ·
        refine ⟨30722636413605064241174321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20481757609070042827449547 30722636413605064241174321)
        ·
          refine ⟨23041977310203798180880741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30722636413605064241174321 23041977310203798180880741)
          ·
            refine ⟨4320370745663212158915139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23041977310203798180880741 4320370745663212158915139)
            ·
              refine ⟨6480556118494818238372709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320370745663212158915139 6480556118494818238372709)
              ·
                refine ⟨1215104272217778419694883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6480556118494818238372709 1215104272217778419694883)
                ·
                  refine ⟨1822656408326667629542325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215104272217778419694883 1822656408326667629542325)
                  ·
                    refine ⟨170874038280625090269593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1822656408326667629542325 170874038280625090269593)
                    ·
                      rfl

theorem cell23_998328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_998328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998328 prefixEnd_998328 := by exact prefixLift 998328
  have htrace : WordTrace (prefixWord ++ tailWord_998328) baseStart_998328 baseEnd_998328 := by
    simpa [prefixWord, tailWord_998328, baseEnd_998328] using wordTrace_append hprefix tailTrace_998328
  have hstable : (prefixWord ++ tailWord_998328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998328).length < 2 ^ (prefixWord ++ tailWord_998328).sum := by decide
  have hdescent : baseEnd_998328 < baseStart_998328 := by decide
  rcases family_descends (prefixWord ++ tailWord_998328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998378 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_998378 : Nat := 118140960795 + 998378 * 2 ^ 59
def prefixEnd_998378 : Nat := 4983230072969 + 3 ^ 40 * 998378 * 2
def baseEnd_998378 : Nat := 512647788874600075183549

theorem tailTrace_998378 : CollatzResearch.WordTrace tailWord_998378 prefixEnd_998378 512647788874600075183549 := by
  unfold tailWord_998378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9103459294263622558140947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24275891451369660155042525 9103459294263622558140947)
  ·
    refine ⟨13655188941395433837211421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9103459294263622558140947 13655188941395433837211421)
    ·
      refine ⟨5120695853023287688954283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13655188941395433837211421 5120695853023287688954283)
      ·
        refine ⟨7681043779534931533431425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5120695853023287688954283 7681043779534931533431425)
        ·
          refine ⟨5760782834651198650073569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7681043779534931533431425 5760782834651198650073569)
          ·
            refine ⟨4320587125988398987555177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5760782834651198650073569 4320587125988398987555177)
            ·
              refine ⟨3240440344491299240666383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4320587125988398987555177 3240440344491299240666383)
              ·
                refine ⟨4860660516736948860999575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240440344491299240666383 4860660516736948860999575)
                ·
                  refine ⟨7290990775105423291499363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860660516736948860999575 7290990775105423291499363)
                  ·
                    refine ⟨10936486162658134937249045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7290990775105423291499363 10936486162658134937249045)
                    ·
                      refine ⟨512647788874600075183549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10936486162658134937249045 512647788874600075183549)
                      ·
                        rfl

theorem cell23_998378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_998378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998378 prefixEnd_998378 := by exact prefixLift 998378
  have htrace : WordTrace (prefixWord ++ tailWord_998378) baseStart_998378 baseEnd_998378 := by
    simpa [prefixWord, tailWord_998378, baseEnd_998378] using wordTrace_append hprefix tailTrace_998378
  have hstable : (prefixWord ++ tailWord_998378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998378).length < 2 ^ (prefixWord ++ tailWord_998378).sum := by decide
  have hdescent : baseEnd_998378 < baseStart_998378 := by decide
  rcases family_descends (prefixWord ++ tailWord_998378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998385 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_998385 : Nat := 118140960795 + 998385 * 2 ^ 59
def prefixEnd_998385 : Nat := 4983230072969 + 3 ^ 40 * 998385 * 2
def baseEnd_998385 : Nat := 512651383239181547796017

theorem tailTrace_998385 : CollatzResearch.WordTrace tailWord_998385 prefixEnd_998385 512651383239181547796017 := by
  unfold tailWord_998385
  simp only [CollatzResearch.WordTrace]
  refine ⟨36414092488029130428068609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24276061658686086952045739 36414092488029130428068609)
  ·
    refine ⟨27310569366021847821051457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36414092488029130428068609 27310569366021847821051457)
    ·
      refine ⟨20482927024516385865788593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27310569366021847821051457 20482927024516385865788593)
      ·
        refine ⟨15362195268387289399341445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20482927024516385865788593 15362195268387289399341445)
        ·
          refine ⟨2880411612822616762376521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15362195268387289399341445 2880411612822616762376521)
          ·
            refine ⟨2160308709616962571782391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880411612822616762376521 2160308709616962571782391)
            ·
              refine ⟨3240463064425443857673587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160308709616962571782391 3240463064425443857673587)
              ·
                refine ⟨4860694596638165786510381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240463064425443857673587 4860694596638165786510381)
                ·
                  refine ⟨1822760473739312169941393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4860694596638165786510381 1822760473739312169941393)
                  ·
                    refine ⟨1367070355304484127456045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1822760473739312169941393 1367070355304484127456045)
                    ·
                      refine ⟨512651383239181547796017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1367070355304484127456045 512651383239181547796017)
                      ·
                        rfl

theorem cell23_998385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_998385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998385 prefixEnd_998385 := by exact prefixLift 998385
  have htrace : WordTrace (prefixWord ++ tailWord_998385) baseStart_998385 baseEnd_998385 := by
    simpa [prefixWord, tailWord_998385, baseEnd_998385] using wordTrace_append hprefix tailTrace_998385
  have hstable : (prefixWord ++ tailWord_998385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998385).length < 2 ^ (prefixWord ++ tailWord_998385).sum := by decide
  have hdescent : baseEnd_998385 < baseStart_998385 := by decide
  rcases family_descends (prefixWord ++ tailWord_998385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998425 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 3, 3, 2]
def baseStart_998425 : Nat := 118140960795 + 998425 * 2 ^ 59
def prefixEnd_998425 : Nat := 4983230072969 + 3 ^ 40 * 998425 * 2
def baseEnd_998425 : Nat := 512671922465361391295833

theorem tailTrace_998425 : CollatzResearch.WordTrace tailWord_998425 prefixEnd_998425 512671922465361391295833 := by
  unfold tailWord_998425
  simp only [CollatzResearch.WordTrace]
  refine ⟨36415551407884217259524729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24277034271922811506349819 36415551407884217259524729)
  ·
    refine ⟨27311663555913162944643547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36415551407884217259524729 27311663555913162944643547)
    ·
      refine ⟨40967495333869744416965321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27311663555913162944643547 40967495333869744416965321)
      ·
        refine ⟨30725621500402308312723991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40967495333869744416965321 30725621500402308312723991)
        ·
          refine ⟨46088432250603462469085987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30725621500402308312723991 46088432250603462469085987)
          ·
            refine ⟨69132648375905193703628981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46088432250603462469085987 69132648375905193703628981)
            ·
              refine ⟨6481185785241111909715217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69132648375905193703628981 6481185785241111909715217)
              ·
                refine ⟨4860889338930833932286413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6481185785241111909715217 4860889338930833932286413)
                ·
                  refine ⟨1822833502099062724607405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4860889338930833932286413 1822833502099062724607405)
                  ·
                    refine ⟨683562563287148521727777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1822833502099062724607405 683562563287148521727777)
                    ·
                      refine ⟨512671922465361391295833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 683562563287148521727777 512671922465361391295833)
                      ·
                        rfl

theorem cell23_998425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_998425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998425 prefixEnd_998425 := by exact prefixLift 998425
  have htrace : WordTrace (prefixWord ++ tailWord_998425) baseStart_998425 baseEnd_998425 := by
    simpa [prefixWord, tailWord_998425, baseEnd_998425] using wordTrace_append hprefix tailTrace_998425
  have hstable : (prefixWord ++ tailWord_998425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998425).length < 2 ^ (prefixWord ++ tailWord_998425).sum := by decide
  have hdescent : baseEnd_998425 < baseStart_998425 := by decide
  rcases family_descends (prefixWord ++ tailWord_998425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998458 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_998458 : Nat := 118140960795 + 998458 * 2 ^ 59
def prefixEnd_998458 : Nat := 4983230072969 + 3 ^ 40 * 998458 * 2
def baseEnd_998458 : Nat := 512688867326959762183181

theorem tailTrace_998458 : CollatzResearch.WordTrace tailWord_998458 prefixEnd_998458 512688867326959762183181 := by
  unfold tailWord_998458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9104188754191165973869007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24277836677843109263650685 9104188754191165973869007)
  ·
    refine ⟨13656283131286748960803511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9104188754191165973869007 13656283131286748960803511)
    ·
      refine ⟨20484424696930123441205267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13656283131286748960803511 20484424696930123441205267)
      ·
        refine ⟨30726637045395185161807901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20484424696930123441205267 30726637045395185161807901)
        ·
          refine ⟨11522488892023194435677963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30726637045395185161807901 11522488892023194435677963)
          ·
            refine ⟨17283733338034791653516945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11522488892023194435677963 17283733338034791653516945)
            ·
              refine ⟨12962800003526093740137709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17283733338034791653516945 12962800003526093740137709)
              ·
                refine ⟨4861050001322285152551641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12962800003526093740137709 4861050001322285152551641)
                ·
                  refine ⟨3645787500991713864413731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4861050001322285152551641 3645787500991713864413731)
                  ·
                    refine ⟨5468681251487570796620597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3645787500991713864413731 5468681251487570796620597)
                    ·
                      refine ⟨512688867326959762183181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5468681251487570796620597 512688867326959762183181)
                      ·
                        rfl

theorem cell23_998458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_998458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998458 prefixEnd_998458 := by exact prefixLift 998458
  have htrace : WordTrace (prefixWord ++ tailWord_998458) baseStart_998458 baseEnd_998458 := by
    simpa [prefixWord, tailWord_998458, baseEnd_998458] using wordTrace_append hprefix tailTrace_998458
  have hstable : (prefixWord ++ tailWord_998458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998458).length < 2 ^ (prefixWord ++ tailWord_998458).sum := by decide
  have hdescent : baseEnd_998458 < baseStart_998458 := by decide
  rcases family_descends (prefixWord ++ tailWord_998458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998472 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_998472 : Nat := 118140960795 + 998472 * 2 ^ 59
def prefixEnd_998472 : Nat := 4983230072969 + 3 ^ 40 * 998472 * 2
def baseEnd_998472 : Nat := 512696056056122707408117

theorem tailTrace_998472 : CollatzResearch.WordTrace tailWord_998472 prefixEnd_998472 512696056056122707408117 := by
  unfold tailWord_998472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18208632819356972143242835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24278177092475962857657113 18208632819356972143242835)
  ·
    refine ⟨27312949229035458214864253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18208632819356972143242835 27312949229035458214864253)
    ·
      refine ⟨10242355960888296830574095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27312949229035458214864253 10242355960888296830574095)
      ·
        refine ⟨15363533941332445245861143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10242355960888296830574095 15363533941332445245861143)
        ·
          refine ⟨23045300911998667868791715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15363533941332445245861143 23045300911998667868791715)
          ·
            refine ⟨34567951367998001803187573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23045300911998667868791715 34567951367998001803187573)
            ·
              refine ⟨3240745440749812669048835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34567951367998001803187573 3240745440749812669048835)
              ·
                refine ⟨4861118161124719003573253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240745440749812669048835 4861118161124719003573253)
                ·
                  refine ⟨911459655210884813169985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4861118161124719003573253 911459655210884813169985)
                  ·
                    refine ⟨683594741408163609877489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 911459655210884813169985 683594741408163609877489)
                    ·
                      refine ⟨512696056056122707408117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 683594741408163609877489 512696056056122707408117)
                      ·
                        rfl

theorem cell23_998472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_998472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998472 prefixEnd_998472 := by exact prefixLift 998472
  have htrace : WordTrace (prefixWord ++ tailWord_998472) baseStart_998472 baseEnd_998472 := by
    simpa [prefixWord, tailWord_998472, baseEnd_998472] using wordTrace_append hprefix tailTrace_998472
  have hstable : (prefixWord ++ tailWord_998472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998472).length < 2 ^ (prefixWord ++ tailWord_998472).sum := by decide
  have hdescent : baseEnd_998472 < baseStart_998472 := by decide
  rcases family_descends (prefixWord ++ tailWord_998472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998508 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_998508 : Nat := 118140960795 + 998508 * 2 ^ 59
def prefixEnd_998508 : Nat := 4983230072969 + 3 ^ 40 * 998508 * 2
def baseEnd_998508 : Nat := 170904847119894855519317

theorem tailTrace_998508 : CollatzResearch.WordTrace tailWord_998508 prefixEnd_998508 170904847119894855519317 := by
  unfold tailWord_998508
  simp only [CollatzResearch.WordTrace]
  refine ⟨18209289333291761217398089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24279052444389014956530785 18209289333291761217398089)
  ·
    refine ⟨13656966999968820913048567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18209289333291761217398089 13656966999968820913048567)
    ·
      refine ⟨20485450499953231369572851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13656966999968820913048567 20485450499953231369572851)
      ·
        refine ⟨30728175749929847054359277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20485450499953231369572851 30728175749929847054359277)
        ·
          refine ⟨11523065906223692645384729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30728175749929847054359277 11523065906223692645384729)
          ·
            refine ⟨8642299429667769484038547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11523065906223692645384729 8642299429667769484038547)
            ·
              refine ⟨12963449144501654226057821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8642299429667769484038547 12963449144501654226057821)
              ·
                refine ⟨4861293429188120334771683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12963449144501654226057821 4861293429188120334771683)
                ·
                  refine ⟨7291940143782180502157525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861293429188120334771683 7291940143782180502157525)
                  ·
                    refine ⟨170904847119894855519317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7291940143782180502157525 170904847119894855519317)
                    ·
                      rfl

theorem cell23_998508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_998508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998508 prefixEnd_998508 := by exact prefixLift 998508
  have htrace : WordTrace (prefixWord ++ tailWord_998508) baseStart_998508 baseEnd_998508 := by
    simpa [prefixWord, tailWord_998508, baseEnd_998508] using wordTrace_append hprefix tailTrace_998508
  have hstable : (prefixWord ++ tailWord_998508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998508).length < 2 ^ (prefixWord ++ tailWord_998508).sum := by decide
  have hdescent : baseEnd_998508 < baseStart_998508 := by decide
  rcases family_descends (prefixWord ++ tailWord_998508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998525 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_998525 : Nat := 118140960795 + 998525 * 2 ^ 59
def prefixEnd_998525 : Nat := 4983230072969 + 3 ^ 40 * 998525 * 2
def baseEnd_998525 : Nat := 170907756843603666681791

theorem tailTrace_998525 : CollatzResearch.WordTrace tailWord_998525 prefixEnd_998525 170907756843603666681791 := by
  unfold tailWord_998525
  simp only [CollatzResearch.WordTrace]
  refine ⟨36419198707521934338165029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24279465805014622892110019 36419198707521934338165029)
  ·
    refine ⟨6828599757660362688405943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36419198707521934338165029 6828599757660362688405943)
    ·
      refine ⟨10242899636490544032608915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6828599757660362688405943 10242899636490544032608915)
      ·
        refine ⟨15364349454735816048913373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10242899636490544032608915 15364349454735816048913373)
        ·
          refine ⟨5761631045525931018342515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15364349454735816048913373 5761631045525931018342515)
          ·
            refine ⟨8642446568288896527513773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761631045525931018342515 8642446568288896527513773)
            ·
              refine ⟨3240917463108336197817665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8642446568288896527513773 3240917463108336197817665)
              ·
                refine ⟨2430688097331252148363249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3240917463108336197817665 2430688097331252148363249)
                ·
                  refine ⟨1823016072998439111272437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2430688097331252148363249 1823016072998439111272437)
                  ·
                    refine ⟨170907756843603666681791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1823016072998439111272437 170907756843603666681791)
                    ·
                      rfl

theorem cell23_998525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_998525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998525 prefixEnd_998525 := by exact prefixLift 998525
  have htrace : WordTrace (prefixWord ++ tailWord_998525) baseStart_998525 baseEnd_998525 := by
    simpa [prefixWord, tailWord_998525, baseEnd_998525] using wordTrace_append hprefix tailTrace_998525
  have hstable : (prefixWord ++ tailWord_998525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998525).length < 2 ^ (prefixWord ++ tailWord_998525).sum := by decide
  have hdescent : baseEnd_998525 < baseStart_998525 := by decide
  rcases family_descends (prefixWord ++ tailWord_998525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998529 : List Nat := [1, 2, 4, 2, 2, 2, 3, 2, 5]
def baseStart_998529 : Nat := 118140960795 + 998529 * 2 ^ 59
def prefixEnd_998529 : Nat := 4983230072969 + 3 ^ 40 * 998529 * 2
def baseEnd_998529 : Nat := 56969480494825442710595

theorem tailTrace_998529 : CollatzResearch.WordTrace tailWord_998529 prefixEnd_998529 56969480494825442710595 := by
  unfold tailWord_998529
  simp only [CollatzResearch.WordTrace]
  refine ⟨36419344599507443021310641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24279563066338295347540427 36419344599507443021310641)
  ·
    refine ⟨27314508449630582265982981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36419344599507443021310641 27314508449630582265982981)
    ·
      refine ⟨5121470334305734174871809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27314508449630582265982981 5121470334305734174871809)
      ·
        refine ⟨3841102750729300631153857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5121470334305734174871809 3841102750729300631153857)
        ·
          refine ⟨2880827063046975473365393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3841102750729300631153857 2880827063046975473365393)
          ·
            refine ⟨2160620297285231605024045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880827063046975473365393 2160620297285231605024045)
            ·
              refine ⟨810232611481961851884017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2160620297285231605024045 810232611481961851884017)
              ·
                refine ⟨607674458611471388913013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810232611481961851884017 607674458611471388913013)
                ·
                  refine ⟨56969480494825442710595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 607674458611471388913013 56969480494825442710595)
                  ·
                    rfl

theorem cell23_998529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 5].length) (baseStart_998529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998529 prefixEnd_998529 := by exact prefixLift 998529
  have htrace : WordTrace (prefixWord ++ tailWord_998529) baseStart_998529 baseEnd_998529 := by
    simpa [prefixWord, tailWord_998529, baseEnd_998529] using wordTrace_append hprefix tailTrace_998529
  have hstable : (prefixWord ++ tailWord_998529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998529).length < 2 ^ (prefixWord ++ tailWord_998529).sum := by decide
  have hdescent : baseEnd_998529 < baseStart_998529 := by decide
  rcases family_descends (prefixWord ++ tailWord_998529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998585 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 6]
def baseStart_998585 : Nat := 118140960795 + 998585 * 2 ^ 59
def prefixEnd_998585 : Nat := 4983230072969 + 3 ^ 40 * 998585 * 2
def baseEnd_998585 : Nat := 56972675485564529477233

theorem tailTrace_998585 : CollatzResearch.WordTrace tailWord_998585 prefixEnd_998585 56972675485564529477233 := by
  unfold tailWord_998585
  simp only [CollatzResearch.WordTrace]
  refine ⟨36421387087304564585349209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24280924724869709723566139 36421387087304564585349209)
  ·
    refine ⟨27316040315478423439011907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36421387087304564585349209 27316040315478423439011907)
    ·
      refine ⟨40974060473217635158517861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27316040315478423439011907 40974060473217635158517861)
      ·
        refine ⟨7682636338728306592222099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40974060473217635158517861 7682636338728306592222099)
        ·
          refine ⟨11523954508092459888333149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7682636338728306592222099 11523954508092459888333149)
          ·
            refine ⟨4321482940534672458124931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11523954508092459888333149 4321482940534672458124931)
            ·
              refine ⟨6482224410802008687187397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321482940534672458124931 6482224410802008687187397)
              ·
                refine ⟨1215417077025376628847637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6482224410802008687187397 1215417077025376628847637)
                ·
                  refine ⟨56972675485564529477233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1215417077025376628847637 56972675485564529477233)
                  ·
                    rfl

theorem cell23_998585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 6].length) (baseStart_998585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998585 prefixEnd_998585 := by exact prefixLift 998585
  have htrace : WordTrace (prefixWord ++ tailWord_998585) baseStart_998585 baseEnd_998585 := by
    simpa [prefixWord, tailWord_998585, baseEnd_998585] using wordTrace_append hprefix tailTrace_998585
  have hstable : (prefixWord ++ tailWord_998585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998585).length < 2 ^ (prefixWord ++ tailWord_998585).sum := by decide
  have hdescent : baseEnd_998585 < baseStart_998585 := by decide
  rcases family_descends (prefixWord ++ tailWord_998585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998615 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 3, 5]
def baseStart_998615 : Nat := 118140960795 + 998615 * 2 ^ 59
def prefixEnd_998615 : Nat := 4983230072969 + 3 ^ 40 * 998615 * 2
def baseEnd_998615 : Nat := 170923161263238549306653

theorem tailTrace_998615 : CollatzResearch.WordTrace tailWord_998615 prefixEnd_998615 170923161263238549306653 := by
  unfold tailWord_998615
  simp only [CollatzResearch.WordTrace]
  refine ⟨36422481277195879708941299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24281654184797253139294199 36422481277195879708941299)
  ·
    refine ⟨54633721915793819563411949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36422481277195879708941299 54633721915793819563411949)
    ·
      refine ⟨20487645718422682336279481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54633721915793819563411949 20487645718422682336279481)
      ·
        refine ⟨15365734288817011752209611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20487645718422682336279481 15365734288817011752209611)
        ·
          refine ⟨23048601433225517628314417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15365734288817011752209611 23048601433225517628314417)
          ·
            refine ⟨17286451074919138221235813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23048601433225517628314417 17286451074919138221235813)
            ·
              refine ⟨3241209576547338416481715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17286451074919138221235813 3241209576547338416481715)
              ·
                refine ⟨4861814364821007624722573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241209576547338416481715 4861814364821007624722573)
                ·
                  refine ⟨1823180386807877859270965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4861814364821007624722573 1823180386807877859270965)
                  ·
                    refine ⟨170923161263238549306653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1823180386807877859270965 170923161263238549306653)
                    ·
                      rfl

theorem cell23_998615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_998615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998615 prefixEnd_998615 := by exact prefixLift 998615
  have htrace : WordTrace (prefixWord ++ tailWord_998615) baseStart_998615 baseEnd_998615 := by
    simpa [prefixWord, tailWord_998615, baseEnd_998615] using wordTrace_append hprefix tailTrace_998615
  have hstable : (prefixWord ++ tailWord_998615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998615).length < 2 ^ (prefixWord ++ tailWord_998615).sum := by decide
  have hdescent : baseEnd_998615 < baseStart_998615 := by decide
  rcases family_descends (prefixWord ++ tailWord_998615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998616 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 2, 2, 3]
def baseStart_998616 : Nat := 118140960795 + 998616 * 2 ^ 59
def prefixEnd_998616 : Nat := 4983230072969 + 3 ^ 40 * 998616 * 2
def baseEnd_998616 : Nat := 512769997270370144007455

theorem tailTrace_998616 : CollatzResearch.WordTrace tailWord_998616 prefixEnd_998616 512769997270370144007455 := by
  unfold tailWord_998616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18211258875096128439863851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24281678500128171253151801 18211258875096128439863851)
  ·
    refine ⟨27316888312644192659795777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18211258875096128439863851 27316888312644192659795777)
    ·
      refine ⟨20487666234483144494846833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27316888312644192659795777 20487666234483144494846833)
      ·
        refine ⟨15365749675862358371135125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20487666234483144494846833 15365749675862358371135125)
        ·
          refine ⟨720269516056048048646959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15365749675862358371135125 720269516056048048646959)
          ·
            refine ⟨1080404274084072072970439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720269516056048048646959 1080404274084072072970439)
            ·
              refine ⟨1620606411126108109455659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080404274084072072970439 1620606411126108109455659)
              ·
                refine ⟨2430909616689162164183489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620606411126108109455659 2430909616689162164183489)
                ·
                  refine ⟨1823182212516871623137617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2430909616689162164183489 1823182212516871623137617)
                  ·
                    refine ⟨1367386659387653717353213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1823182212516871623137617 1367386659387653717353213)
                    ·
                      refine ⟨512769997270370144007455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1367386659387653717353213 512769997270370144007455)
                      ·
                        rfl

theorem cell23_998616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_998616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998616 prefixEnd_998616 := by exact prefixLift 998616
  have htrace : WordTrace (prefixWord ++ tailWord_998616) baseStart_998616 baseEnd_998616 := by
    simpa [prefixWord, tailWord_998616, baseEnd_998616] using wordTrace_append hprefix tailTrace_998616
  have hstable : (prefixWord ++ tailWord_998616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998616).length < 2 ^ (prefixWord ++ tailWord_998616).sum := by decide
  have hdescent : baseEnd_998616 < baseStart_998616 := by decide
  rcases family_descends (prefixWord ++ tailWord_998616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998632 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 1, 5]
def baseStart_998632 : Nat := 118140960795 + 998632 * 2 ^ 59
def prefixEnd_998632 : Nat := 4983230072969 + 3 ^ 40 * 998632 * 2
def baseEnd_998632 : Nat := 170926070986947360469127

theorem tailTrace_998632 : CollatzResearch.WordTrace tailWord_998632 prefixEnd_998632 170926070986947360469127 := by
  unfold tailWord_998632
  simp only [CollatzResearch.WordTrace]
  refine ⟨18211550659067145806155075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24282067545422861074873433 18211550659067145806155075)
  ·
    refine ⟨27317325988600718709232613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18211550659067145806155075 27317325988600718709232613)
    ·
      refine ⟨5121998622862634757981115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27317325988600718709232613 5121998622862634757981115)
      ·
        refine ⟨7682997934293952136971673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121998622862634757981115 7682997934293952136971673)
        ·
          refine ⟨5762248450720464102728755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7682997934293952136971673 5762248450720464102728755)
          ·
            refine ⟨8643372676080696154093133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5762248450720464102728755 8643372676080696154093133)
            ·
              refine ⟨3241264753530261057784925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8643372676080696154093133 3241264753530261057784925)
              ·
                refine ⟨1215474282573847896669347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3241264753530261057784925 1215474282573847896669347)
                ·
                  refine ⟨1823211423860771845004021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215474282573847896669347 1823211423860771845004021)
                  ·
                    refine ⟨170926070986947360469127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1823211423860771845004021 170926070986947360469127)
                    ·
                      rfl

theorem cell23_998632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_998632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998632 prefixEnd_998632 := by exact prefixLift 998632
  have htrace : WordTrace (prefixWord ++ tailWord_998632) baseStart_998632 baseEnd_998632 := by
    simpa [prefixWord, tailWord_998632, baseEnd_998632] using wordTrace_append hprefix tailTrace_998632
  have hstable : (prefixWord ++ tailWord_998632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998632).length < 2 ^ (prefixWord ++ tailWord_998632).sum := by decide
  have hdescent : baseEnd_998632 < baseStart_998632 := by decide
  rcases family_descends (prefixWord ++ tailWord_998632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998655 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_998655 : Nat := 118140960795 + 998655 * 2 ^ 59
def prefixEnd_998655 : Nat := 4983230072969 + 3 ^ 40 * 998655 * 2
def baseEnd_998655 : Nat := 512790023015895491419775

theorem tailTrace_998655 : CollatzResearch.WordTrace tailWord_998655 prefixEnd_998655 512790023015895491419775 := by
  unfold tailWord_998655
  simp only [CollatzResearch.WordTrace]
  refine ⟨36423940197050966540397419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24282626798033977693598279 36423940197050966540397419)
  ·
    refine ⟨54635910295576449810596129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36423940197050966540397419 54635910295576449810596129)
    ·
      refine ⟨40976932721682337357947097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54635910295576449810596129 40976932721682337357947097)
      ·
        refine ⟨30732699541261753018460323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40976932721682337357947097 30732699541261753018460323)
        ·
          refine ⟨46099049311892629527690485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30732699541261753018460323 46099049311892629527690485)
          ·
            refine ⟨4321785872989934018220983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46099049311892629527690485 4321785872989934018220983)
            ·
              refine ⟨6482678809484901027331475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321785872989934018220983 6482678809484901027331475)
              ·
                refine ⟨9724018214227351540997213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482678809484901027331475 9724018214227351540997213)
                ·
                  refine ⟨3646506830335256827873955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9724018214227351540997213 3646506830335256827873955)
                  ·
                    refine ⟨5469760245502885241810933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3646506830335256827873955 5469760245502885241810933)
                    ·
                      refine ⟨512790023015895491419775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5469760245502885241810933 512790023015895491419775)
                      ·
                        rfl

theorem cell23_998655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_998655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998655 prefixEnd_998655 := by exact prefixLift 998655
  have htrace : WordTrace (prefixWord ++ tailWord_998655) baseStart_998655 baseEnd_998655 := by
    simpa [prefixWord, tailWord_998655, baseEnd_998655] using wordTrace_append hprefix tailTrace_998655
  have hstable : (prefixWord ++ tailWord_998655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998655).length < 2 ^ (prefixWord ++ tailWord_998655).sum := by decide
  have hdescent : baseEnd_998655 < baseStart_998655 := by decide
  rcases family_descends (prefixWord ++ tailWord_998655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998665 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_998665 : Nat := 118140960795 + 998665 * 2 ^ 59
def prefixEnd_998665 : Nat := 4983230072969 + 3 ^ 40 * 998665 * 2
def baseEnd_998665 : Nat := 512795157822440452294729

theorem tailTrace_998665 : CollatzResearch.WordTrace tailWord_998665 prefixEnd_998665 512795157822440452294729 := by
  unfold tailWord_998665
  simp only [CollatzResearch.WordTrace]
  refine ⟨36424304927014738248261449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24282869951343158832174299 36424304927014738248261449)
  ·
    refine ⟨27318228695261053686196087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36424304927014738248261449 27318228695261053686196087)
    ·
      refine ⟨40977343042891580529294131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27318228695261053686196087 40977343042891580529294131)
      ·
        refine ⟨61466014564337370793941197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40977343042891580529294131 61466014564337370793941197)
        ·
          refine ⟨23049755461626514047727949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61466014564337370793941197 23049755461626514047727949)
          ·
            refine ⟨8643658298109942767897981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23049755461626514047727949 8643658298109942767897981)
            ·
              refine ⟨3241371861791228537961743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8643658298109942767897981 3241371861791228537961743)
              ·
                refine ⟨4862057792686842806942615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241371861791228537961743 4862057792686842806942615)
                ·
                  refine ⟨7293086689030264210413923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862057792686842806942615 7293086689030264210413923)
                  ·
                    refine ⟨10939630033545396315620885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7293086689030264210413923 10939630033545396315620885)
                    ·
                      refine ⟨512795157822440452294729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10939630033545396315620885 512795157822440452294729)
                      ·
                        rfl

theorem cell23_998665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_998665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998665 prefixEnd_998665 := by exact prefixLift 998665
  have htrace : WordTrace (prefixWord ++ tailWord_998665) baseStart_998665 baseEnd_998665 := by
    simpa [prefixWord, tailWord_998665, baseEnd_998665] using wordTrace_append hprefix tailTrace_998665
  have hstable : (prefixWord ++ tailWord_998665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998665).length < 2 ^ (prefixWord ++ tailWord_998665).sum := by decide
  have hdescent : baseEnd_998665 < baseStart_998665 := by decide
  rcases family_descends (prefixWord ++ tailWord_998665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998712 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 2, 7, 2]
def baseStart_998712 : Nat := 118140960795 + 998712 * 2 ^ 59
def prefixEnd_998712 : Nat := 4983230072969 + 3 ^ 40 * 998712 * 2
def baseEnd_998712 : Nat := 512819291413201768407013

theorem tailTrace_998712 : CollatzResearch.WordTrace tailWord_998712 prefixEnd_998712 512819291413201768407013 := by
  unfold tailWord_998712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18213009578922232637611195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24284012771896310183481593 18213009578922232637611195)
  ·
    refine ⟨27319514368383348956416793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18213009578922232637611195 27319514368383348956416793)
    ·
      refine ⟨20489635776287511717312595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27319514368383348956416793 20489635776287511717312595)
      ·
        refine ⟨30734453664431267575968893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20489635776287511717312595 30734453664431267575968893)
        ·
          refine ⟨11525420124161725340988335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30734453664431267575968893 11525420124161725340988335)
          ·
            refine ⟨17288130186242588011482503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11525420124161725340988335 17288130186242588011482503)
            ·
              refine ⟨25932195279363882017223755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17288130186242588011482503 25932195279363882017223755)
              ·
                refine ⟨38898292919045823025835633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25932195279363882017223755 38898292919045823025835633)
                ·
                  refine ⟨29173719689284367269376725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38898292919045823025835633 29173719689284367269376725)
                  ·
                    refine ⟨683759055217602357876017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29173719689284367269376725 683759055217602357876017)
                    ·
                      refine ⟨512819291413201768407013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 683759055217602357876017 512819291413201768407013)
                      ·
                        rfl

theorem cell23_998712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_998712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998712 prefixEnd_998712 := by exact prefixLift 998712
  have htrace : WordTrace (prefixWord ++ tailWord_998712) baseStart_998712 baseEnd_998712 := by
    simpa [prefixWord, tailWord_998712, baseEnd_998712] using wordTrace_append hprefix tailTrace_998712
  have hstable : (prefixWord ++ tailWord_998712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998712).length < 2 ^ (prefixWord ++ tailWord_998712).sum := by decide
  have hdescent : baseEnd_998712 < baseStart_998712 := by decide
  rcases family_descends (prefixWord ++ tailWord_998712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998713 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 2, 4]
def baseStart_998713 : Nat := 118140960795 + 998713 * 2 ^ 59
def prefixEnd_998713 : Nat := 4983230072969 + 3 ^ 40 * 998713 * 2
def baseEnd_998713 : Nat := 170939934964618754831503

theorem tailTrace_998713 : CollatzResearch.WordTrace tailWord_998713 prefixEnd_998713 170939934964618754831503 := by
  unfold tailWord_998713
  simp only [CollatzResearch.WordTrace]
  refine ⟨36426055630840842446008793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24284037087227228297339195 36426055630840842446008793)
  ·
    refine ⟨27319541723130631834506595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36426055630840842446008793 27319541723130631834506595)
    ·
      refine ⟨40979312584695947751759893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27319541723130631834506595 40979312584695947751759893)
      ·
        refine ⟨1920905277407622550863745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40979312584695947751759893 1920905277407622550863745)
        ·
          refine ⟨1440678958055716913147809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1920905277407622550863745 1440678958055716913147809)
          ·
            refine ⟨1080509218541787684860857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1440678958055716913147809 1080509218541787684860857)
            ·
              refine ⟨810381913906340763645643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080509218541787684860857 810381913906340763645643)
              ·
                refine ⟨1215572870859511145468465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810381913906340763645643 1215572870859511145468465)
                ·
                  refine ⟨911679653144633359101349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1215572870859511145468465 911679653144633359101349)
                  ·
                    refine ⟨170939934964618754831503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 911679653144633359101349 170939934964618754831503)
                    ·
                      rfl

theorem cell23_998713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 4].length) (baseStart_998713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998713 prefixEnd_998713 := by exact prefixLift 998713
  have htrace : WordTrace (prefixWord ++ tailWord_998713) baseStart_998713 baseEnd_998713 := by
    simpa [prefixWord, tailWord_998713, baseEnd_998713] using wordTrace_append hprefix tailTrace_998713
  have hstable : (prefixWord ++ tailWord_998713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998713).length < 2 ^ (prefixWord ++ tailWord_998713).sum := by decide
  have hdescent : baseEnd_998713 < baseStart_998713 := by decide
  rcases family_descends (prefixWord ++ tailWord_998713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998829 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_998829 : Nat := 118140960795 + 998829 * 2 ^ 59
def prefixEnd_998829 : Nat := 4983230072969 + 3 ^ 40 * 998829 * 2
def baseEnd_998829 : Nat := 170959789549925936881325

theorem tailTrace_998829 : CollatzResearch.WordTrace tailWord_998829 prefixEnd_998829 170959789549925936881325 := by
  unfold tailWord_998829
  simp only [CollatzResearch.WordTrace]
  refine ⟨36430286498420594257231541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24286857665613729504821027 36430286498420594257231541)
  ·
    refine ⟨3415339359226930711615457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36430286498420594257231541 3415339359226930711615457)
    ·
      refine ⟨2561504519420198033711593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3415339359226930711615457 2561504519420198033711593)
      ·
        refine ⟨1921128389565148525283695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2561504519420198033711593 1921128389565148525283695)
        ·
          refine ⟨2881692584347722787925543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921128389565148525283695 2881692584347722787925543)
          ·
            refine ⟨4322538876521584181888315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881692584347722787925543 4322538876521584181888315)
            ·
              refine ⟨6483808314782376272832473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322538876521584181888315 6483808314782376272832473)
              ·
                refine ⟨4862856236086782204624355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483808314782376272832473 4862856236086782204624355)
                ·
                  refine ⟨7294284354130173306936533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862856236086782204624355 7294284354130173306936533)
                  ·
                    refine ⟨170959789549925936881325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7294284354130173306936533 170959789549925936881325)
                    ·
                      rfl

theorem cell23_998829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_998829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998829 prefixEnd_998829 := by exact prefixLift 998829
  have htrace : WordTrace (prefixWord ++ tailWord_998829) baseStart_998829 baseEnd_998829 := by
    simpa [prefixWord, tailWord_998829, baseEnd_998829] using wordTrace_append hprefix tailTrace_998829
  have hstable : (prefixWord ++ tailWord_998829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998829).length < 2 ^ (prefixWord ++ tailWord_998829).sum := by decide
  have hdescent : baseEnd_998829 < baseStart_998829 := by decide
  rcases family_descends (prefixWord ++ tailWord_998829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998832 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_998832 : Nat := 118140960795 + 998832 * 2 ^ 59
def prefixEnd_998832 : Nat := 4983230072969 + 3 ^ 40 * 998832 * 2
def baseEnd_998832 : Nat := 512880909091741298906461

theorem tailTrace_998832 : CollatzResearch.WordTrace tailWord_998832 prefixEnd_998832 512880909091741298906461 := by
  unfold tailWord_998832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18215197958704862884795375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24286930611606483846393833 18215197958704862884795375)
  ·
    refine ⟨27322796938057294327193063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18215197958704862884795375 27322796938057294327193063)
    ·
      refine ⟨40984195407085941490789595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27322796938057294327193063 40984195407085941490789595)
      ·
        refine ⟨61476293110628912236184393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40984195407085941490789595 61476293110628912236184393)
        ·
          refine ⟨46107219832971684177138295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61476293110628912236184393 46107219832971684177138295)
          ·
            refine ⟨69160829749457526265707443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46107219832971684177138295 69160829749457526265707443)
            ·
              refine ⟨103741244624186289398561165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69160829749457526265707443 103741244624186289398561165)
              ·
                refine ⟨38902966734069858524460437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103741244624186289398561165 38902966734069858524460437)
                ·
                  refine ⟨1823576565659524618334083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38902966734069858524460437 1823576565659524618334083)
                  ·
                    refine ⟨2735364848489286927501125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1823576565659524618334083 2735364848489286927501125)
                    ·
                      refine ⟨512880909091741298906461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2735364848489286927501125 512880909091741298906461)
                      ·
                        rfl

theorem cell23_998832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_998832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998832 prefixEnd_998832 := by exact prefixLift 998832
  have htrace : WordTrace (prefixWord ++ tailWord_998832) baseStart_998832 baseEnd_998832 := by
    simpa [prefixWord, tailWord_998832, baseEnd_998832] using wordTrace_append hprefix tailTrace_998832
  have hstable : (prefixWord ++ tailWord_998832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998832).length < 2 ^ (prefixWord ++ tailWord_998832).sum := by decide
  have hdescent : baseEnd_998832 < baseStart_998832 := by decide
  rcases family_descends (prefixWord ++ tailWord_998832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998862 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_998862 : Nat := 118140960795 + 998862 * 2 ^ 59
def prefixEnd_998862 : Nat := 4983230072969 + 3 ^ 40 * 998862 * 2
def baseEnd_998862 : Nat := 512896313511376181531323

theorem tailTrace_998862 : CollatzResearch.WordTrace tailWord_998862 prefixEnd_998862 512896313511376181531323 := by
  unfold tailWord_998862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553936263412630111647855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24287660071534027262121893 4553936263412630111647855)
  ·
    refine ⟨6830904395118945167471783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4553936263412630111647855 6830904395118945167471783)
    ·
      refine ⟨10246356592678417751207675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830904395118945167471783 10246356592678417751207675)
      ·
        refine ⟨15369534889017626626811513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10246356592678417751207675 15369534889017626626811513)
        ·
          refine ⟨11527151166763219970108635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15369534889017626626811513 11527151166763219970108635)
          ·
            refine ⟨17290726750144829955162953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11527151166763219970108635 17290726750144829955162953)
            ·
              refine ⟨12968045062608622466372215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17290726750144829955162953 12968045062608622466372215)
              ·
                refine ⟨19452067593912933699558323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12968045062608622466372215 19452067593912933699558323)
                ·
                  refine ⟨29178101390869400549337485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19452067593912933699558323 29178101390869400549337485)
                  ·
                    refine ⟨10941788021576025206001557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29178101390869400549337485 10941788021576025206001557)
                    ·
                      refine ⟨512896313511376181531323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10941788021576025206001557 512896313511376181531323)
                      ·
                        rfl

theorem cell23_998862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_998862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998862 prefixEnd_998862 := by exact prefixLift 998862
  have htrace : WordTrace (prefixWord ++ tailWord_998862) baseStart_998862 baseEnd_998862 := by
    simpa [prefixWord, tailWord_998862, baseEnd_998862] using wordTrace_append hprefix tailTrace_998862
  have hstable : (prefixWord ++ tailWord_998862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998862).length < 2 ^ (prefixWord ++ tailWord_998862).sum := by decide
  have hdescent : baseEnd_998862 < baseStart_998862 := by decide
  rcases family_descends (prefixWord ++ tailWord_998862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998872 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 8]
def baseStart_998872 : Nat := 118140960795 + 998872 * 2 ^ 59
def prefixEnd_998872 : Nat := 4983230072969 + 3 ^ 40 * 998872 * 2
def baseEnd_998872 : Nat := 56989049813102349156253

theorem tailTrace_998872 : CollatzResearch.WordTrace tailWord_998872 prefixEnd_998872 56989049813102349156253 := by
  unfold tailWord_998872
  simp only [CollatzResearch.WordTrace]
  refine ⟨18215927418632406300523435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24287903224843208400697913 18215927418632406300523435)
  ·
    refine ⟨27323891127948609450785153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18215927418632406300523435 27323891127948609450785153)
    ·
      refine ⟨20492918345961457088088865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27323891127948609450785153 20492918345961457088088865)
      ·
        refine ⟨15369688759471092816066649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20492918345961457088088865 15369688759471092816066649)
        ·
          refine ⟨11527266569603319612049987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15369688759471092816066649 11527266569603319612049987)
          ·
            refine ⟨17290899854404979418074981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11527266569603319612049987 17290899854404979418074981)
            ·
              refine ⟨3242043722700933640889059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17290899854404979418074981 3242043722700933640889059)
              ·
                refine ⟨4863065584051400461333589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3242043722700933640889059 4863065584051400461333589)
                ·
                  refine ⟨56989049813102349156253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4863065584051400461333589 56989049813102349156253)
                  ·
                    rfl

theorem cell23_998872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 8].length) (baseStart_998872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998872 prefixEnd_998872 := by exact prefixLift 998872
  have htrace : WordTrace (prefixWord ++ tailWord_998872) baseStart_998872 baseEnd_998872 := by
    simpa [prefixWord, tailWord_998872, baseEnd_998872] using wordTrace_append hprefix tailTrace_998872
  have hstable : (prefixWord ++ tailWord_998872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998872).length < 2 ^ (prefixWord ++ tailWord_998872).sum := by decide
  have hdescent : baseEnd_998872 < baseStart_998872 := by decide
  rcases family_descends (prefixWord ++ tailWord_998872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998949 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_998949 : Nat := 118140960795 + 998949 * 2 ^ 59
def prefixEnd_998949 : Nat := 4983230072969 + 3 ^ 40 * 998949 * 2
def baseEnd_998949 : Nat := 170980328776105780381141

theorem tailTrace_998949 : CollatzResearch.WordTrace tailWord_998949 prefixEnd_998949 170980328776105780381141 := by
  unfold tailWord_998949
  simp only [CollatzResearch.WordTrace]
  refine ⟨36434663257985854751599901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24289775505323903167733267 36434663257985854751599901)
  ·
    refine ⟨13662998721744695531849963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36434663257985854751599901 13662998721744695531849963)
    ·
      refine ⟨20494498082617043297774945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13662998721744695531849963 20494498082617043297774945)
      ·
        refine ⟨15370873561962782473331209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20494498082617043297774945 15370873561962782473331209)
        ·
          refine ⟨11528155171472086854998407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15370873561962782473331209 11528155171472086854998407)
          ·
            refine ⟨17292232757208130282497611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11528155171472086854998407 17292232757208130282497611)
            ·
              refine ⟨25938349135812195423746417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17292232757208130282497611 25938349135812195423746417)
              ·
                refine ⟨19453761851859146567809813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25938349135812195423746417 19453761851859146567809813)
                ·
                  refine ⟨911895086805897495366085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19453761851859146567809813 911895086805897495366085)
                  ·
                    refine ⟨170980328776105780381141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 911895086805897495366085 170980328776105780381141)
                    ·
                      rfl

theorem cell23_998949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_998949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998949 prefixEnd_998949 := by exact prefixLift 998949
  have htrace : WordTrace (prefixWord ++ tailWord_998949) baseStart_998949 baseEnd_998949 := by
    simpa [prefixWord, tailWord_998949, baseEnd_998949] using wordTrace_append hprefix tailTrace_998949
  have hstable : (prefixWord ++ tailWord_998949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998949).length < 2 ^ (prefixWord ++ tailWord_998949).sum := by decide
  have hdescent : baseEnd_998949 < baseStart_998949 := by decide
  rcases family_descends (prefixWord ++ tailWord_998949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998973 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_998973 : Nat := 118140960795 + 998973 * 2 ^ 59
def prefixEnd_998973 : Nat := 4983230072969 + 3 ^ 40 * 998973 * 2
def baseEnd_998973 : Nat := 512953309864025247243313

theorem tailTrace_998973 : CollatzResearch.WordTrace tailWord_998973 prefixEnd_998973 512953309864025247243313 := by
  unfold tailWord_998973
  simp only [CollatzResearch.WordTrace]
  refine ⟨36435538609898906850473573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24290359073265937900315715 36435538609898906850473573)
  ·
    refine ⟨6831663489356045034463795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36435538609898906850473573 6831663489356045034463795)
    ·
      refine ⟨10247495234034067551695693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6831663489356045034463795 10247495234034067551695693)
      ·
        refine ⟨3842810712762775331885885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10247495234034067551695693 3842810712762775331885885)
        ·
          refine ⟨1441054017286040749457207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3842810712762775331885885 1441054017286040749457207)
          ·
            refine ⟨2161581025929061124185811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441054017286040749457207 2161581025929061124185811)
            ·
              refine ⟨3242371538893591686278717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161581025929061124185811 3242371538893591686278717)
              ·
                refine ⟨1215889327085096882354519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3242371538893591686278717 1215889327085096882354519)
                ·
                  refine ⟨1823833990627645323531779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215889327085096882354519 1823833990627645323531779)
                  ·
                    refine ⟨2735750985941467985297669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1823833990627645323531779 2735750985941467985297669)
                    ·
                      refine ⟨512953309864025247243313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2735750985941467985297669 512953309864025247243313)
                      ·
                        rfl

theorem cell23_998973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_998973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_998973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_998973 prefixEnd_998973 := by exact prefixLift 998973
  have htrace : WordTrace (prefixWord ++ tailWord_998973) baseStart_998973 baseEnd_998973 := by
    simpa [prefixWord, tailWord_998973, baseEnd_998973] using wordTrace_append hprefix tailTrace_998973
  have hstable : (prefixWord ++ tailWord_998973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998973).length < 2 ^ (prefixWord ++ tailWord_998973).sum := by decide
  have hdescent : baseEnd_998973 < baseStart_998973 := by decide
  rcases family_descends (prefixWord ++ tailWord_998973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999033 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 1, 3, 2]
def baseStart_999033 : Nat := 118140960795 + 999033 * 2 ^ 59
def prefixEnd_999033 : Nat := 4983230072969 + 3 ^ 40 * 999033 * 2
def baseEnd_999033 : Nat := 512984118703295012493037

theorem tailTrace_999033 : CollatzResearch.WordTrace tailWord_999033 prefixEnd_999033 512984118703295012493037 := by
  unfold tailWord_999033
  simp only [CollatzResearch.WordTrace]
  refine ⟨36437726989681537097657753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24291817993121024731771835 36437726989681537097657753)
  ·
    refine ⟨27328295242261152823243315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36437726989681537097657753 27328295242261152823243315)
    ·
      refine ⟨40992442863391729234864973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27328295242261152823243315 40992442863391729234864973)
      ·
        refine ⟨15372166073771898463074365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40992442863391729234864973 15372166073771898463074365)
        ·
          refine ⟨5764562277664461923652887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15372166073771898463074365 5764562277664461923652887)
          ·
            refine ⟨8646843416496692885479331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764562277664461923652887 8646843416496692885479331)
            ·
              refine ⟨12970265124745039328218997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8646843416496692885479331 12970265124745039328218997)
              ·
                refine ⟨1215962355444847437020531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12970265124745039328218997 1215962355444847437020531)
                ·
                  refine ⟨1823943533167271155530797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215962355444847437020531 1823943533167271155530797)
                  ·
                    refine ⟨683978824937726683324049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1823943533167271155530797 683978824937726683324049)
                    ·
                      refine ⟨512984118703295012493037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 683978824937726683324049 512984118703295012493037)
                      ·
                        rfl

theorem cell23_999033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_999033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999033 prefixEnd_999033 := by exact prefixLift 999033
  have htrace : WordTrace (prefixWord ++ tailWord_999033) baseStart_999033 baseEnd_999033 := by
    simpa [prefixWord, tailWord_999033, baseEnd_999033] using wordTrace_append hprefix tailTrace_999033
  have hstable : (prefixWord ++ tailWord_999033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999033).length < 2 ^ (prefixWord ++ tailWord_999033).sum := by decide
  have hdescent : baseEnd_999033 < baseStart_999033 := by decide
  rcases family_descends (prefixWord ++ tailWord_999033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999069 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 9]
def baseStart_999069 : Nat := 118140960795 + 999069 * 2 ^ 59
def prefixEnd_999069 : Nat := 4983230072969 + 3 ^ 40 * 999069 * 2
def baseEnd_999069 : Nat := 57000289334095207960319

theorem tailTrace_999069 : CollatzResearch.WordTrace tailWord_999069 prefixEnd_999069 57000289334095207960319 := by
  unfold tailWord_999069
  simp only [CollatzResearch.WordTrace]
  refine ⟨36439040017551115245968261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24292693345034076830645507 36439040017551115245968261)
  ·
    refine ⟨6832320003290834108619049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36439040017551115245968261 6832320003290834108619049)
    ·
      refine ⟨5124240002468125581464287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6832320003290834108619049 5124240002468125581464287)
      ·
        refine ⟨7686360003702188372196431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124240002468125581464287 7686360003702188372196431)
        ·
          refine ⟨11529540005553282558294647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7686360003702188372196431 11529540005553282558294647)
          ·
            refine ⟨17294310008329923837441971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529540005553282558294647 17294310008329923837441971)
            ·
              refine ⟨25941465012494885756162957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17294310008329923837441971 25941465012494885756162957)
              ·
                refine ⟨9728049379685582158561109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25941465012494885756162957 9728049379685582158561109)
                ·
                  refine ⟨57000289334095207960319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9728049379685582158561109 57000289334095207960319)
                  ·
                    rfl

theorem cell23_999069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_999069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999069 prefixEnd_999069 := by exact prefixLift 999069
  have htrace : WordTrace (prefixWord ++ tailWord_999069) baseStart_999069 baseEnd_999069 := by
    simpa [prefixWord, tailWord_999069, baseEnd_999069] using wordTrace_append hprefix tailTrace_999069
  have hstable : (prefixWord ++ tailWord_999069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999069).length < 2 ^ (prefixWord ++ tailWord_999069).sum := by decide
  have hdescent : baseEnd_999069 < baseStart_999069 := by decide
  rcases family_descends (prefixWord ++ tailWord_999069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999110 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_999110 : Nat := 118140960795 + 999110 * 2 ^ 59
def prefixEnd_999110 : Nat := 4983230072969 + 3 ^ 40 * 999110 * 2
def baseEnd_999110 : Nat := 513023656713691211230183

theorem tailTrace_999110 : CollatzResearch.WordTrace tailWord_999110 prefixEnd_999110 513023656713691211230183 := by
  unfold tailWord_999110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138766731575080601506587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24293690273601719498807189 1138766731575080601506587)
  ·
    refine ⟨1708150097362620902259881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1138766731575080601506587 1708150097362620902259881)
    ·
      refine ⟨1281112573021965676694911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1708150097362620902259881 1281112573021965676694911)
      ·
        refine ⟨1921668859532948515042367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281112573021965676694911 1921668859532948515042367)
        ·
          refine ⟨2882503289299422772563551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921668859532948515042367 2882503289299422772563551)
          ·
            refine ⟨4323754933949134158845327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882503289299422772563551 4323754933949134158845327)
            ·
              refine ⟨6485632400923701238267991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323754933949134158845327 6485632400923701238267991)
              ·
                refine ⟨9728448601385551857401987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6485632400923701238267991 9728448601385551857401987)
                ·
                  refine ⟨14592672902078327786102981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9728448601385551857401987 14592672902078327786102981)
                  ·
                    refine ⟨2736126169139686459894309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14592672902078327786102981 2736126169139686459894309)
                    ·
                      refine ⟨513023656713691211230183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2736126169139686459894309 513023656713691211230183)
                      ·
                        rfl

theorem cell23_999110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_999110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999110 prefixEnd_999110 := by exact prefixLift 999110
  have htrace : WordTrace (prefixWord ++ tailWord_999110) baseStart_999110 baseEnd_999110 := by
    simpa [prefixWord, tailWord_999110, baseEnd_999110] using wordTrace_append hprefix tailTrace_999110
  have hstable : (prefixWord ++ tailWord_999110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999110).length < 2 ^ (prefixWord ++ tailWord_999110).sum := by decide
  have hdescent : baseEnd_999110 < baseStart_999110 := by decide
  rcases family_descends (prefixWord ++ tailWord_999110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999153 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 2, 4, 2]
def baseStart_999153 : Nat := 118140960795 + 999153 * 2 ^ 59
def prefixEnd_999153 : Nat := 4983230072969 + 3 ^ 40 * 999153 * 2
def baseEnd_999153 : Nat := 513045736381834542992485

theorem tailTrace_999153 : CollatzResearch.WordTrace tailWord_999153 prefixEnd_999153 513045736381834542992485 := by
  unfold tailWord_999153
  simp only [CollatzResearch.WordTrace]
  refine ⟨36442103749246797592026113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24294735832831198394684075 36442103749246797592026113)
  ·
    refine ⟨27331577811935098194019585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36442103749246797592026113 27331577811935098194019585)
    ·
      refine ⟨20498683358951323645514689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27331577811935098194019585 20498683358951323645514689)
      ·
        refine ⟨15374012519213492734136017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20498683358951323645514689 15374012519213492734136017)
        ·
          refine ⟨11530509389410119550602013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15374012519213492734136017 11530509389410119550602013)
          ·
            refine ⟨4323941021028794831475755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11530509389410119550602013 4323941021028794831475755)
            ·
              refine ⟨6485911531543192247213633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323941021028794831475755 6485911531543192247213633)
              ·
                refine ⟨4864433648657394185410225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6485911531543192247213633 4864433648657394185410225)
                ·
                  refine ⟨3648325236493045639057669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4864433648657394185410225 3648325236493045639057669)
                  ·
                    refine ⟨684060981842446057323313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3648325236493045639057669 684060981842446057323313)
                    ·
                      refine ⟨513045736381834542992485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 684060981842446057323313 513045736381834542992485)
                      ·
                        rfl

theorem cell23_999153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_999153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999153 prefixEnd_999153 := by exact prefixLift 999153
  have htrace : WordTrace (prefixWord ++ tailWord_999153) baseStart_999153 baseEnd_999153 := by
    simpa [prefixWord, tailWord_999153, baseEnd_999153] using wordTrace_append hprefix tailTrace_999153
  have hstable : (prefixWord ++ tailWord_999153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999153).length < 2 ^ (prefixWord ++ tailWord_999153).sum := by decide
  have hdescent : baseEnd_999153 < baseStart_999153 := by decide
  rcases family_descends (prefixWord ++ tailWord_999153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999170 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_999170 : Nat := 118140960795 + 999170 * 2 ^ 59
def prefixEnd_999170 : Nat := 4983230072969 + 3 ^ 40 * 999170 * 2
def baseEnd_999170 : Nat := 513054465552960976479907

theorem tailTrace_999170 : CollatzResearch.WordTrace tailWord_999170 prefixEnd_999170 513054465552960976479907 := by
  unfold tailWord_999170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110680947546302373848741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24295149193456806330263309 9110680947546302373848741)
  ·
    refine ⟨1708252677664931695096639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9110680947546302373848741 1708252677664931695096639)
    ·
      refine ⟨2562379016497397542644959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1708252677664931695096639 2562379016497397542644959)
      ·
        refine ⟨3843568524746096313967439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2562379016497397542644959 3843568524746096313967439)
        ·
          refine ⟨5765352787119144470951159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843568524746096313967439 5765352787119144470951159)
          ·
            refine ⟨8648029180678716706426739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765352787119144470951159 8648029180678716706426739)
            ·
              refine ⟨12972043771018075059640109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648029180678716706426739 12972043771018075059640109)
              ·
                refine ⟨4864516414131778147365041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12972043771018075059640109 4864516414131778147365041)
                ·
                  refine ⟨3648387310598833610523781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4864516414131778147365041 3648387310598833610523781)
                  ·
                    refine ⟨684072620737281301973209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3648387310598833610523781 684072620737281301973209)
                    ·
                      refine ⟨513054465552960976479907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 684072620737281301973209 513054465552960976479907)
                      ·
                        rfl

theorem cell23_999170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_999170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999170 prefixEnd_999170 := by exact prefixLift 999170
  have htrace : WordTrace (prefixWord ++ tailWord_999170) baseStart_999170 baseEnd_999170 := by
    simpa [prefixWord, tailWord_999170, baseEnd_999170] using wordTrace_append hprefix tailTrace_999170
  have hstable : (prefixWord ++ tailWord_999170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999170).length < 2 ^ (prefixWord ++ tailWord_999170).sum := by decide
  have hdescent : baseEnd_999170 < baseStart_999170 := by decide
  rcases family_descends (prefixWord ++ tailWord_999170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999203 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 3]
def baseStart_999203 : Nat := 118140960795 + 999203 * 2 ^ 59
def prefixEnd_999203 : Nat := 4983230072969 + 3 ^ 40 * 999203 * 2
def baseEnd_999203 : Nat := 513071410414559347367255

theorem tailTrace_999203 : CollatzResearch.WordTrace tailWord_999203 prefixEnd_999203 513071410414559347367255 := by
  unfold tailWord_999203
  simp only [CollatzResearch.WordTrace]
  refine ⟨36443927399065656131346263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24295951599377104087564175 36443927399065656131346263)
  ·
    refine ⟨54665891098598484197019395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36443927399065656131346263 54665891098598484197019395)
    ·
      refine ⟨81998836647897726295529093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54665891098598484197019395 81998836647897726295529093)
      ·
        refine ⟨15374781871480823680411705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81998836647897726295529093 15374781871480823680411705)
        ·
          refine ⟨11531086403610617760308779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15374781871480823680411705 11531086403610617760308779)
          ·
            refine ⟨17296629605415926640463169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11531086403610617760308779 17296629605415926640463169)
            ·
              refine ⟨12972472204061944980347377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17296629605415926640463169 12972472204061944980347377)
              ·
                refine ⟨9729354153046458735260533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12972472204061944980347377 9729354153046458735260533)
                ·
                  refine ⟨912126951848105506430675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9729354153046458735260533 912126951848105506430675)
                  ·
                    refine ⟨1368190427772158259646013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 912126951848105506430675 1368190427772158259646013)
                    ·
                      refine ⟨513071410414559347367255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1368190427772158259646013 513071410414559347367255)
                      ·
                        rfl

theorem cell23_999203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_999203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999203 prefixEnd_999203 := by exact prefixLift 999203
  have htrace : WordTrace (prefixWord ++ tailWord_999203) baseStart_999203 baseEnd_999203 := by
    simpa [prefixWord, tailWord_999203, baseEnd_999203] using wordTrace_append hprefix tailTrace_999203
  have hstable : (prefixWord ++ tailWord_999203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999203).length < 2 ^ (prefixWord ++ tailWord_999203).sum := by decide
  have hdescent : baseEnd_999203 < baseStart_999203 := by decide
  rcases family_descends (prefixWord ++ tailWord_999203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999214 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_999214 : Nat := 118140960795 + 999214 * 2 ^ 59
def prefixEnd_999214 : Nat := 4983230072969 + 3 ^ 40 * 999214 * 2
def baseEnd_999214 : Nat := 171025686233919601443235

theorem tailTrace_999214 : CollatzResearch.WordTrace tailWord_999214 prefixEnd_999214 171025686233919601443235 := by
  unfold tailWord_999214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4555541075253225626249587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24296219068017203339997797 4555541075253225626249587)
  ·
    refine ⟨6833311612879838439374381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4555541075253225626249587 6833311612879838439374381)
    ·
      refine ⟨2562491854829939414765393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6833311612879838439374381 2562491854829939414765393)
      ·
        refine ⟨1921868891122454561074045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2562491854829939414765393 1921868891122454561074045)
        ·
          refine ⟨720700834170920460402767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1921868891122454561074045 720700834170920460402767)
          ·
            refine ⟨1081051251256380690604151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720700834170920460402767 1081051251256380690604151)
            ·
              refine ⟨1621576876884571035906227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081051251256380690604151 1621576876884571035906227)
              ·
                refine ⟨2432365315326856553859341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621576876884571035906227 2432365315326856553859341)
                ·
                  refine ⟨912136993247571207697253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2432365315326856553859341 912136993247571207697253)
                  ·
                    refine ⟨171025686233919601443235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 912136993247571207697253 171025686233919601443235)
                    ·
                      rfl

theorem cell23_999214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_999214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999214 prefixEnd_999214 := by exact prefixLift 999214
  have htrace : WordTrace (prefixWord ++ tailWord_999214) baseStart_999214 baseEnd_999214 := by
    simpa [prefixWord, tailWord_999214, baseEnd_999214] using wordTrace_append hprefix tailTrace_999214
  have hstable : (prefixWord ++ tailWord_999214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999214).length < 2 ^ (prefixWord ++ tailWord_999214).sum := by decide
  have hdescent : baseEnd_999214 < baseStart_999214 := by decide
  rcases family_descends (prefixWord ++ tailWord_999214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999240 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 1, 5]
def baseStart_999240 : Nat := 118140960795 + 999240 * 2 ^ 59
def prefixEnd_999240 : Nat := 4983230072969 + 3 ^ 40 * 999240 * 2
def baseEnd_999240 : Nat := 171030136399591900868195

theorem tailTrace_999240 : CollatzResearch.WordTrace tailWord_999240 prefixEnd_999240 171030136399591900868195 := by
  unfold tailWord_999240
  simp only [CollatzResearch.WordTrace]
  refine ⟨18222638449965805725221587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24296851266621074300295449 18222638449965805725221587)
  ·
    refine ⟨27333957674948708587832381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18222638449965805725221587 27333957674948708587832381)
    ·
      refine ⟨10250234128105765720437143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27333957674948708587832381 10250234128105765720437143)
      ·
        refine ⟨15375351192158648580655715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10250234128105765720437143 15375351192158648580655715)
        ·
          refine ⟨23063026788237972870983573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15375351192158648580655715 23063026788237972870983573)
          ·
            refine ⟨1081079380698654978327355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23063026788237972870983573 1081079380698654978327355)
            ·
              refine ⟨1621619071047982467491033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081079380698654978327355 1621619071047982467491033)
              ·
                refine ⟨1216214303285986850618275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621619071047982467491033 1216214303285986850618275)
                ·
                  refine ⟨1824321454928980275927413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216214303285986850618275 1824321454928980275927413)
                  ·
                    refine ⟨171030136399591900868195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1824321454928980275927413 171030136399591900868195)
                    ·
                      rfl

theorem cell23_999240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_999240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999240 prefixEnd_999240 := by exact prefixLift 999240
  have htrace : WordTrace (prefixWord ++ tailWord_999240) baseStart_999240 baseEnd_999240 := by
    simpa [prefixWord, tailWord_999240, baseEnd_999240] using wordTrace_append hprefix tailTrace_999240
  have hstable : (prefixWord ++ tailWord_999240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999240).length < 2 ^ (prefixWord ++ tailWord_999240).sum := by decide
  have hdescent : baseEnd_999240 < baseStart_999240 := by decide
  rcases family_descends (prefixWord ++ tailWord_999240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999246 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_999246 : Nat := 118140960795 + 999246 * 2 ^ 59
def prefixEnd_999246 : Nat := 4983230072969 + 3 ^ 40 * 999246 * 2
def baseEnd_999246 : Nat := 513093490082702679129557

theorem tailTrace_999246 : CollatzResearch.WordTrace tailWord_999246 prefixEnd_999246 513093490082702679129557 := by
  unfold tailWord_999246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4555686967238734309395199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24296997158606582983441061 4555686967238734309395199)
  ·
    refine ⟨6833530450858101464092799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4555686967238734309395199 6833530450858101464092799)
    ·
      refine ⟨10250295676287152196139199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6833530450858101464092799 10250295676287152196139199)
      ·
        refine ⟨15375443514430728294208799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10250295676287152196139199 15375443514430728294208799)
        ·
          refine ⟨23063165271646092441313199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15375443514430728294208799 23063165271646092441313199)
          ·
            refine ⟨34594747907469138661969799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23063165271646092441313199 34594747907469138661969799)
            ·
              refine ⟨51892121861203707992954699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34594747907469138661969799 51892121861203707992954699)
              ·
                refine ⟨77838182791805561989432049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51892121861203707992954699 77838182791805561989432049)
                ·
                  refine ⟨58378637093854171492074037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77838182791805561989432049 58378637093854171492074037)
                  ·
                    refine ⟨5472997227548828577381941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58378637093854171492074037 5472997227548828577381941)
                    ·
                      refine ⟨513093490082702679129557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5472997227548828577381941 513093490082702679129557)
                      ·
                        rfl

theorem cell23_999246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_999246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999246 prefixEnd_999246 := by exact prefixLift 999246
  have htrace : WordTrace (prefixWord ++ tailWord_999246) baseStart_999246 baseEnd_999246 := by
    simpa [prefixWord, tailWord_999246, baseEnd_999246] using wordTrace_append hprefix tailTrace_999246
  have hstable : (prefixWord ++ tailWord_999246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999246).length < 2 ^ (prefixWord ++ tailWord_999246).sum := by decide
  have hdescent : baseEnd_999246 < baseStart_999246 := by decide
  rcases family_descends (prefixWord ++ tailWord_999246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999253 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_999253 : Nat := 118140960795 + 999253 * 2 ^ 59
def prefixEnd_999253 : Nat := 4983230072969 + 3 ^ 40 * 999253 * 2
def baseEnd_999253 : Nat := 171032361482428050580675

theorem tailTrace_999253 : CollatzResearch.WordTrace tailWord_999253 prefixEnd_999253 171032361482428050580675 := by
  unfold tailWord_999253
  simp only [CollatzResearch.WordTrace]
  refine ⟨36445751048884514670666413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24297167365923009780444275 36445751048884514670666413)
  ·
    refine ⟨13667156643331693001499905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36445751048884514670666413 13667156643331693001499905)
    ·
      refine ⟨10250367482498769751124929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13667156643331693001499905 10250367482498769751124929)
      ·
        refine ⟨7687775611874077313343697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10250367482498769751124929 7687775611874077313343697)
        ·
          refine ⟨5765831708905557985007773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7687775611874077313343697 5765831708905557985007773)
          ·
            refine ⟨2162186890839584244377915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5765831708905557985007773 2162186890839584244377915)
            ·
              refine ⟨3243280336259376366566873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162186890839584244377915 3243280336259376366566873)
              ·
                refine ⟨2432460252194532274925155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3243280336259376366566873 2432460252194532274925155)
                ·
                  refine ⟨3648690378291798412387733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432460252194532274925155 3648690378291798412387733)
                  ·
                    refine ⟨171032361482428050580675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3648690378291798412387733 171032361482428050580675)
                    ·
                      rfl

theorem cell23_999253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_999253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999253 prefixEnd_999253 := by exact prefixLift 999253
  have htrace : WordTrace (prefixWord ++ tailWord_999253) baseStart_999253 baseEnd_999253 := by
    simpa [prefixWord, tailWord_999253, baseEnd_999253] using wordTrace_append hprefix tailTrace_999253
  have hstable : (prefixWord ++ tailWord_999253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999253).length < 2 ^ (prefixWord ++ tailWord_999253).sum := by decide
  have hdescent : baseEnd_999253 < baseStart_999253 := by decide
  rcases family_descends (prefixWord ++ tailWord_999253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999263 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 5]
def baseStart_999263 : Nat := 118140960795 + 999263 * 2 ^ 59
def prefixEnd_999263 : Nat := 4983230072969 + 3 ^ 40 * 999263 * 2
def baseEnd_999263 : Nat := 513102219253829112616979

theorem tailTrace_999263 : CollatzResearch.WordTrace tailWord_999263 prefixEnd_999263 513102219253829112616979 := by
  unfold tailWord_999263
  simp only [CollatzResearch.WordTrace]
  refine ⟨36446115778848286378530443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24297410519232190919020295 36446115778848286378530443)
  ·
    refine ⟨54669173668272429567795665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36446115778848286378530443 54669173668272429567795665)
    ·
      refine ⟨41001880251204322175846749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54669173668272429567795665 41001880251204322175846749)
      ·
        refine ⟨15375705094201620815942531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41001880251204322175846749 15375705094201620815942531)
        ·
          refine ⟨23063557641302431223913797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15375705094201620815942531 23063557641302431223913797)
          ·
            refine ⟨4324417057744205854483837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23063557641302431223913797 4324417057744205854483837)
            ·
              refine ⟨1621656396654077195431439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4324417057744205854483837 1621656396654077195431439)
              ·
                refine ⟨2432484594981115793147159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621656396654077195431439 2432484594981115793147159)
                ·
                  refine ⟨3648726892471673689720739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432484594981115793147159 3648726892471673689720739)
                  ·
                    refine ⟨5473090338707510534581109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3648726892471673689720739 5473090338707510534581109)
                    ·
                      refine ⟨513102219253829112616979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5473090338707510534581109 513102219253829112616979)
                      ·
                        rfl

theorem cell23_999263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_999263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999263 prefixEnd_999263 := by exact prefixLift 999263
  have htrace : WordTrace (prefixWord ++ tailWord_999263) baseStart_999263 baseEnd_999263 := by
    simpa [prefixWord, tailWord_999263, baseEnd_999263] using wordTrace_append hprefix tailTrace_999263
  have hstable : (prefixWord ++ tailWord_999263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999263).length < 2 ^ (prefixWord ++ tailWord_999263).sum := by decide
  have hdescent : baseEnd_999263 < baseStart_999263 := by decide
  rcases family_descends (prefixWord ++ tailWord_999263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999294 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_999294 : Nat := 118140960795 + 999294 * 2 ^ 59
def prefixEnd_999294 : Nat := 4983230072969 + 3 ^ 40 * 999294 * 2
def baseEnd_999294 : Nat := 513118137154118491329337

theorem tailTrace_999294 : CollatzResearch.WordTrace tailWord_999294 prefixEnd_999294 513118137154118491329337 := by
  unfold tailWord_999294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4555905805216997334113617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24298164294490652448605957 4555905805216997334113617)
  ·
    refine ⟨3416929353912748000585213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4555905805216997334113617 3416929353912748000585213)
    ·
      refine ⟨1281348507717280500219455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3416929353912748000585213 1281348507717280500219455)
      ·
        refine ⟨1922022761575920750329183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281348507717280500219455 1922022761575920750329183)
        ·
          refine ⟨2883034142363881125493775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922022761575920750329183 2883034142363881125493775)
          ·
            refine ⟨4324551213545821688240663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883034142363881125493775 4324551213545821688240663)
            ·
              refine ⟨6486826820318732532360995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324551213545821688240663 6486826820318732532360995)
              ·
                refine ⟨9730240230478098798541493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6486826820318732532360995 9730240230478098798541493)
                ·
                  refine ⟨912210021607321762363265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9730240230478098798541493 912210021607321762363265)
                  ·
                    refine ⟨684157516205491321772449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 912210021607321762363265 684157516205491321772449)
                    ·
                      refine ⟨513118137154118491329337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 684157516205491321772449 513118137154118491329337)
                      ·
                        rfl

theorem cell23_999294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_999294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999294 prefixEnd_999294 := by exact prefixLift 999294
  have htrace : WordTrace (prefixWord ++ tailWord_999294) baseStart_999294 baseEnd_999294 := by
    simpa [prefixWord, tailWord_999294, baseEnd_999294] using wordTrace_append hprefix tailTrace_999294
  have hstable : (prefixWord ++ tailWord_999294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999294).length < 2 ^ (prefixWord ++ tailWord_999294).sum := by decide
  have hdescent : baseEnd_999294 < baseStart_999294 := by decide
  rcases family_descends (prefixWord ++ tailWord_999294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999296 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 2, 7]
def baseStart_999296 : Nat := 118140960795 + 999296 * 2 ^ 59
def prefixEnd_999296 : Nat := 4983230072969 + 3 ^ 40 * 999296 * 2
def baseEnd_999296 : Nat := 171039721371809161168109

theorem tailTrace_999296 : CollatzResearch.WordTrace tailWord_999296 prefixEnd_999296 171039721371809161168109 := by
  unfold tailWord_999296
  simp only [CollatzResearch.WordTrace]
  refine ⟨18223659693864366507240871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24298212925152488676321161 18223659693864366507240871)
  ·
    refine ⟨27335489540796549760861307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18223659693864366507240871 27335489540796549760861307)
    ·
      refine ⟨41003234311194824641291961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27335489540796549760861307 41003234311194824641291961)
      ·
        refine ⟨30752425733396118480968971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41003234311194824641291961 30752425733396118480968971)
        ·
          refine ⟨46128638600094177721453457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30752425733396118480968971 46128638600094177721453457)
          ·
            refine ⟨34596478950070633291090093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46128638600094177721453457 34596478950070633291090093)
            ·
              refine ⟨12973679606276487484158785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34596478950070633291090093 12973679606276487484158785)
              ·
                refine ⟨9730259704707365613119089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12973679606276487484158785 9730259704707365613119089)
                ·
                  refine ⟨7297694778530524209839317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9730259704707365613119089 7297694778530524209839317)
                  ·
                    refine ⟨171039721371809161168109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7297694778530524209839317 171039721371809161168109)
                    ·
                      rfl

theorem cell23_999296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_999296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999296 prefixEnd_999296 := by exact prefixLift 999296
  have htrace : WordTrace (prefixWord ++ tailWord_999296) baseStart_999296 baseEnd_999296 := by
    simpa [prefixWord, tailWord_999296, baseEnd_999296] using wordTrace_append hprefix tailTrace_999296
  have hstable : (prefixWord ++ tailWord_999296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999296).length < 2 ^ (prefixWord ++ tailWord_999296).sum := by decide
  have hdescent : baseEnd_999296 < baseStart_999296 := by decide
  rcases family_descends (prefixWord ++ tailWord_999296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999314 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_999314 : Nat := 118140960795 + 999314 * 2 ^ 59
def prefixEnd_999314 : Nat := 4983230072969 + 3 ^ 40 * 999314 * 2
def baseEnd_999314 : Nat := 513128406767208413079245

theorem tailTrace_999314 : CollatzResearch.WordTrace tailWord_999314 prefixEnd_999314 513128406767208413079245 := by
  unfold tailWord_999314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9111993975415880522159249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24298650601109014725757997 9111993975415880522159249)
  ·
    refine ⟨6833995481561910391619437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9111993975415880522159249 6833995481561910391619437)
    ·
      refine ⟨2562748305585716396857289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6833995481561910391619437 2562748305585716396857289)
      ·
        refine ⟨1922061229189287297642967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2562748305585716396857289 1922061229189287297642967)
        ·
          refine ⟨2883091843783930946464451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922061229189287297642967 2883091843783930946464451)
          ·
            refine ⟨4324637765675896419696677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883091843783930946464451 4324637765675896419696677)
            ·
              refine ⟨810869581064230578693127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4324637765675896419696677 810869581064230578693127)
              ·
                refine ⟨1216304371596345868039691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810869581064230578693127 1216304371596345868039691)
                ·
                  refine ⟨1824456557394518802059537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216304371596345868039691 1824456557394518802059537)
                  ·
                    refine ⟨1368342418045889101544653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1824456557394518802059537 1368342418045889101544653)
                    ·
                      refine ⟨513128406767208413079245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1368342418045889101544653 513128406767208413079245)
                      ·
                        rfl

theorem cell23_999314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_999314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999314 prefixEnd_999314 := by exact prefixLift 999314
  have htrace : WordTrace (prefixWord ++ tailWord_999314) baseStart_999314 baseEnd_999314 := by
    simpa [prefixWord, tailWord_999314, baseEnd_999314] using wordTrace_append hprefix tailTrace_999314
  have hstable : (prefixWord ++ tailWord_999314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999314).length < 2 ^ (prefixWord ++ tailWord_999314).sum := by decide
  have hdescent : baseEnd_999314 < baseStart_999314 := by decide
  rcases family_descends (prefixWord ++ tailWord_999314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999327 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 3]
def baseStart_999327 : Nat := 118140960795 + 999327 * 2 ^ 59
def prefixEnd_999327 : Nat := 4983230072969 + 3 ^ 40 * 999327 * 2
def baseEnd_999327 : Nat := 513135082015716862216685

theorem tailTrace_999327 : CollatzResearch.WordTrace tailWord_999327 prefixEnd_999327 513135082015716862216685 := by
  unfold tailWord_999327
  simp only [CollatzResearch.WordTrace]
  refine ⟨36448450050616425308860235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24298966700410950205906823 36448450050616425308860235)
  ·
    refine ⟨54672675075924637963290353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36448450050616425308860235 54672675075924637963290353)
    ·
      refine ⟨41004506306943478472467765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54672675075924637963290353 41004506306943478472467765)
      ·
        refine ⟨3844172466275951106793853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41004506306943478472467765 3844172466275951106793853)
        ·
          refine ⟨1441564674853481665047695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3844172466275951106793853 1441564674853481665047695)
          ·
            refine ⟨2162347012280222497571543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441564674853481665047695 2162347012280222497571543)
            ·
              refine ⟨3243520518420333746357315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162347012280222497571543 3243520518420333746357315)
              ·
                refine ⟨4865280777630500619535973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243520518420333746357315 4865280777630500619535973)
                ·
                  refine ⟨912240145805718866162995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4865280777630500619535973 912240145805718866162995)
                  ·
                    refine ⟨1368360218708578299244493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 912240145805718866162995 1368360218708578299244493)
                    ·
                      refine ⟨513135082015716862216685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1368360218708578299244493 513135082015716862216685)
                      ·
                        rfl

theorem cell23_999327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_999327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999327 prefixEnd_999327 := by exact prefixLift 999327
  have htrace : WordTrace (prefixWord ++ tailWord_999327) baseStart_999327 baseEnd_999327 := by
    simpa [prefixWord, tailWord_999327, baseEnd_999327] using wordTrace_append hprefix tailTrace_999327
  have hstable : (prefixWord ++ tailWord_999327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999327).length < 2 ^ (prefixWord ++ tailWord_999327).sum := by decide
  have hdescent : baseEnd_999327 < baseStart_999327 := by decide
  rcases family_descends (prefixWord ++ tailWord_999327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999353 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_999353 : Nat := 118140960795 + 999353 * 2 ^ 59
def prefixEnd_999353 : Nat := 4983230072969 + 3 ^ 40 * 999353 * 2
def baseEnd_999353 : Nat := 513148432512733760491565

theorem tailTrace_999353 : CollatzResearch.WordTrace tailWord_999353 prefixEnd_999353 513148432512733760491565 := by
  unfold tailWord_999353
  simp only [CollatzResearch.WordTrace]
  refine ⟨36449398348522231749306713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24299598899014821166204475 36449398348522231749306713)
  ·
    refine ⟨27337048761391673811980035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36449398348522231749306713 27337048761391673811980035)
    ·
      refine ⟨41005573142087510717970053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27337048761391673811980035 41005573142087510717970053)
      ·
        refine ⟨7688544964141408259619385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41005573142087510717970053 7688544964141408259619385)
        ·
          refine ⟨5766408723106056194714539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7688544964141408259619385 5766408723106056194714539)
          ·
            refine ⟨8649613084659084292071809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766408723106056194714539 8649613084659084292071809)
            ·
              refine ⟨6487209813494313219053857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8649613084659084292071809 6487209813494313219053857)
              ·
                refine ⟨4865407360120734914290393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6487209813494313219053857 4865407360120734914290393)
                ·
                  refine ⟨3649055520090551185717795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4865407360120734914290393 3649055520090551185717795)
                  ·
                    refine ⟨5473583280135826778576693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3649055520090551185717795 5473583280135826778576693)
                    ·
                      refine ⟨513148432512733760491565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5473583280135826778576693 513148432512733760491565)
                      ·
                        rfl

theorem cell23_999353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_999353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999353 prefixEnd_999353 := by exact prefixLift 999353
  have htrace : WordTrace (prefixWord ++ tailWord_999353) baseStart_999353 baseEnd_999353 := by
    simpa [prefixWord, tailWord_999353, baseEnd_999353] using wordTrace_append hprefix tailTrace_999353
  have hstable : (prefixWord ++ tailWord_999353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999353).length < 2 ^ (prefixWord ++ tailWord_999353).sum := by decide
  have hdescent : baseEnd_999353 < baseStart_999353 := by decide
  rcases family_descends (prefixWord ++ tailWord_999353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999420 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_999420 : Nat := 118140960795 + 999420 * 2 ^ 59
def prefixEnd_999420 : Nat := 4983230072969 + 3 ^ 40 * 999420 * 2
def baseEnd_999420 : Nat := 171060945238861666117919

theorem tailTrace_999420 : CollatzResearch.WordTrace tailWord_999420 prefixEnd_999420 171060945238861666117919 := by
  unfold tailWord_999420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18225921019639751095997857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24301228026186334794663809 18225921019639751095997857)
  ·
    refine ⟨13669440764729813321998393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18225921019639751095997857 13669440764729813321998393)
    ·
      refine ⟨10252080573547359991498795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13669440764729813321998393 10252080573547359991498795)
      ·
        refine ⟨15378120860321039987248193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10252080573547359991498795 15378120860321039987248193)
        ·
          refine ⟨11533590645240779990436145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15378120860321039987248193 11533590645240779990436145)
          ·
            refine ⟨8650192983930584992827109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11533590645240779990436145 8650192983930584992827109)
            ·
              refine ⟨1621911184486984686155083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8650192983930584992827109 1621911184486984686155083)
              ·
                refine ⟨2432866776730477029232625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621911184486984686155083 2432866776730477029232625)
                ·
                  refine ⟨1824650082547857771924469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2432866776730477029232625 1824650082547857771924469)
                  ·
                    refine ⟨171060945238861666117919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1824650082547857771924469 171060945238861666117919)
                    ·
                      rfl

theorem cell23_999420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_999420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999420 prefixEnd_999420 := by exact prefixLift 999420
  have htrace : WordTrace (prefixWord ++ tailWord_999420) baseStart_999420 baseEnd_999420 := by
    simpa [prefixWord, tailWord_999420, baseEnd_999420] using wordTrace_append hprefix tailTrace_999420
  have hstable : (prefixWord ++ tailWord_999420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999420).length < 2 ^ (prefixWord ++ tailWord_999420).sum := by decide
  have hdescent : baseEnd_999420 < baseStart_999420 := by decide
  rcases family_descends (prefixWord ++ tailWord_999420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999423 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_999423 : Nat := 118140960795 + 999423 * 2 ^ 59
def prefixEnd_999423 : Nat := 4983230072969 + 3 ^ 40 * 999423 * 2
def baseEnd_999423 : Nat := 513184376158548486616243

theorem tailTrace_999423 : CollatzResearch.WordTrace tailWord_999423 prefixEnd_999423 513184376158548486616243 := by
  unfold tailWord_999423
  simp only [CollatzResearch.WordTrace]
  refine ⟨36451951458268633704354923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24301300972179089136236615 36451951458268633704354923)
  ·
    refine ⟨54677927187402950556532385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36451951458268633704354923 54677927187402950556532385)
    ·
      refine ⟨41008445390552212917399289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54677927187402950556532385 41008445390552212917399289)
      ·
        refine ⟨30756334042914159688049467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41008445390552212917399289 30756334042914159688049467)
        ·
          refine ⟨46134501064371239532074201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30756334042914159688049467 46134501064371239532074201)
          ·
            refine ⟨34600875798278429649055651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46134501064371239532074201 34600875798278429649055651)
            ·
              refine ⟨51901313697417644473583477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34600875798278429649055651 51901313697417644473583477)
              ·
                refine ⟨4865748159132904169398451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51901313697417644473583477 4865748159132904169398451)
                ·
                  refine ⟨7298622238699356254097677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865748159132904169398451 7298622238699356254097677)
                  ·
                    refine ⟨2736983339512258595286629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7298622238699356254097677 2736983339512258595286629)
                    ·
                      refine ⟨513184376158548486616243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2736983339512258595286629 513184376158548486616243)
                      ·
                        rfl

theorem cell23_999423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_999423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999423 prefixEnd_999423 := by exact prefixLift 999423
  have htrace : WordTrace (prefixWord ++ tailWord_999423) baseStart_999423 baseEnd_999423 := by
    simpa [prefixWord, tailWord_999423, baseEnd_999423] using wordTrace_append hprefix tailTrace_999423
  have hstable : (prefixWord ++ tailWord_999423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999423).length < 2 ^ (prefixWord ++ tailWord_999423).sum := by decide
  have hdescent : baseEnd_999423 < baseStart_999423 := by decide
  rcases family_descends (prefixWord ++ tailWord_999423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999440 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 4, 4, 2]
def baseStart_999440 : Nat := 118140960795 + 999440 * 2 ^ 59
def prefixEnd_999440 : Nat := 4983230072969 + 3 ^ 40 * 999440 * 2
def baseEnd_999440 : Nat := 513193105329674920103665

theorem tailTrace_999440 : CollatzResearch.WordTrace tailWord_999440 prefixEnd_999440 513193105329674920103665 := by
  unfold tailWord_999440
  simp only [CollatzResearch.WordTrace]
  refine ⟨18226285749603522803861887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24301714332804697071815849 18226285749603522803861887)
  ·
    refine ⟨27339428624405284205792831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18226285749603522803861887 27339428624405284205792831)
    ·
      refine ⟨41009142936607926308689247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27339428624405284205792831 41009142936607926308689247)
      ·
        refine ⟨61513714404911889463033871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41009142936607926308689247 61513714404911889463033871)
        ·
          refine ⟨92270571607367834194550807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61513714404911889463033871 92270571607367834194550807)
          ·
            refine ⟨138405857411051751291826211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92270571607367834194550807 138405857411051751291826211)
            ·
              refine ⟨207608786116577626937739317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138405857411051751291826211 207608786116577626937739317)
              ·
                refine ⟨19463323698429152525413061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207608786116577626937739317 19463323698429152525413061)
                ·
                  refine ⟨3649373193455466098514949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19463323698429152525413061 3649373193455466098514949)
                  ·
                    refine ⟨684257473772899893471553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3649373193455466098514949 684257473772899893471553)
                    ·
                      refine ⟨513193105329674920103665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 684257473772899893471553 513193105329674920103665)
                      ·
                        rfl

theorem cell23_999440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 4, 2].length) (baseStart_999440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999440 prefixEnd_999440 := by exact prefixLift 999440
  have htrace : WordTrace (prefixWord ++ tailWord_999440) baseStart_999440 baseEnd_999440 := by
    simpa [prefixWord, tailWord_999440, baseEnd_999440] using wordTrace_append hprefix tailTrace_999440
  have hstable : (prefixWord ++ tailWord_999440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999440).length < 2 ^ (prefixWord ++ tailWord_999440).sum := by decide
  have hdescent : baseEnd_999440 < baseStart_999440 := by decide
  rcases family_descends (prefixWord ++ tailWord_999440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999477 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_999477 : Nat := 118140960795 + 999477 * 2 ^ 59
def prefixEnd_999477 : Nat := 4983230072969 + 3 ^ 40 * 999477 * 2
def baseEnd_999477 : Nat := 513212104113891275340995

theorem tailTrace_999477 : CollatzResearch.WordTrace tailWord_999477 prefixEnd_999477 513212104113891275340995 := by
  unfold tailWord_999477
  simp only [CollatzResearch.WordTrace]
  refine ⟨36453921000073000926820685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24302614000048667284547123 36453921000073000926820685)
  ·
    refine ⟨13670220375027375347557757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36453921000073000926820685 13670220375027375347557757)
    ·
      refine ⟨5126332640635265755334159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13670220375027375347557757 5126332640635265755334159)
      ·
        refine ⟨7689498960952898633001239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126332640635265755334159 7689498960952898633001239)
        ·
          refine ⟨11534248441429347949501859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689498960952898633001239 11534248441429347949501859)
          ·
            refine ⟨17301372662144021924252789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11534248441429347949501859 17301372662144021924252789)
            ·
              refine ⟨1622003687076002055398699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17301372662144021924252789 1622003687076002055398699)
              ·
                refine ⟨2433005530614003083098049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622003687076002055398699 2433005530614003083098049)
                ·
                  refine ⟨1824754147960502312323537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2433005530614003083098049 1824754147960502312323537)
                  ·
                    refine ⟨1368565610970376734242653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1824754147960502312323537 1368565610970376734242653)
                    ·
                      refine ⟨513212104113891275340995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1368565610970376734242653 513212104113891275340995)
                      ·
                        rfl

theorem cell23_999477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_999477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999477 prefixEnd_999477 := by exact prefixLift 999477
  have htrace : WordTrace (prefixWord ++ tailWord_999477) baseStart_999477 baseEnd_999477 := by
    simpa [prefixWord, tailWord_999477, baseEnd_999477] using wordTrace_append hprefix tailTrace_999477
  have hstable : (prefixWord ++ tailWord_999477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999477).length < 2 ^ (prefixWord ++ tailWord_999477).sum := by decide
  have hdescent : baseEnd_999477 < baseStart_999477 := by decide
  rcases family_descends (prefixWord ++ tailWord_999477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999484 : List Nat := [2, 2, 2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_999484 : Nat := 118140960795 + 999484 * 2 ^ 59
def prefixEnd_999484 : Nat := 4983230072969 + 3 ^ 40 * 999484 * 2
def baseEnd_999484 : Nat := 171071899492824249317821

theorem tailTrace_999484 : CollatzResearch.WordTrace tailWord_999484 prefixEnd_999484 171071899492824249317821 := by
  unfold tailWord_999484
  simp only [CollatzResearch.WordTrace]
  refine ⟨18227088155523820561162753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24302784207365094081550337 18227088155523820561162753)
  ·
    refine ⟨13670316116642865420872065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18227088155523820561162753 13670316116642865420872065)
    ·
      refine ⟨10252737087482149065654049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13670316116642865420872065 10252737087482149065654049)
      ·
        refine ⟨7689552815611611799240537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10252737087482149065654049 7689552815611611799240537)
        ·
          refine ⟨5767164611708708849430403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7689552815611611799240537 5767164611708708849430403)
          ·
            refine ⟨8650746917563063274145605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767164611708708849430403 8650746917563063274145605)
            ·
              refine ⟨1622015047043074363902301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8650746917563063274145605 1622015047043074363902301)
              ·
                refine ⟨608255642641152886463363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1622015047043074363902301 608255642641152886463363)
                ·
                  refine ⟨912383463961729329695045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608255642641152886463363 912383463961729329695045)
                  ·
                    refine ⟨171071899492824249317821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 912383463961729329695045 171071899492824249317821)
                    ·
                      rfl

theorem cell23_999484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_999484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999484 prefixEnd_999484 := by exact prefixLift 999484
  have htrace : WordTrace (prefixWord ++ tailWord_999484) baseStart_999484 baseEnd_999484 := by
    simpa [prefixWord, tailWord_999484, baseEnd_999484] using wordTrace_append hprefix tailTrace_999484
  have hstable : (prefixWord ++ tailWord_999484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999484).length < 2 ^ (prefixWord ++ tailWord_999484).sum := by decide
  have hdescent : baseEnd_999484 < baseStart_999484 := by decide
  rcases family_descends (prefixWord ++ tailWord_999484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999494 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_999494 : Nat := 118140960795 + 999494 * 2 ^ 59
def prefixEnd_999494 : Nat := 4983230072969 + 3 ^ 40 * 999494 * 2
def baseEnd_999494 : Nat := 513220833285017708828417

theorem tailTrace_999494 : CollatzResearch.WordTrace tailWord_999494 prefixEnd_999494 513220833285017708828417 := by
  unfold tailWord_999494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139204407531606650943423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24303027360674275220126357 1139204407531606650943423)
  ·
    refine ⟨1708806611297409976415135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139204407531606650943423 1708806611297409976415135)
    ·
      refine ⟨2563209916946114964622703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1708806611297409976415135 2563209916946114964622703)
      ·
        refine ⟨3844814875419172446934055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2563209916946114964622703 3844814875419172446934055)
        ·
          refine ⟨5767222313128758670401083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844814875419172446934055 5767222313128758670401083)
          ·
            refine ⟨8650833469693138005601625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767222313128758670401083 8650833469693138005601625)
            ·
              refine ⟨6488125102269853504201219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8650833469693138005601625 6488125102269853504201219)
              ·
                refine ⟨9732187653404780256301829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488125102269853504201219 9732187653404780256301829)
                ·
                  refine ⟨1824785185013396298056593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9732187653404780256301829 1824785185013396298056593)
                  ·
                    refine ⟨1368588888760047223542445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1824785185013396298056593 1368588888760047223542445)
                    ·
                      refine ⟨513220833285017708828417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1368588888760047223542445 513220833285017708828417)
                      ·
                        rfl

theorem cell23_999494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_999494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999494 prefixEnd_999494 := by exact prefixLift 999494
  have htrace : WordTrace (prefixWord ++ tailWord_999494) baseStart_999494 baseEnd_999494 := by
    simpa [prefixWord, tailWord_999494, baseEnd_999494] using wordTrace_append hprefix tailTrace_999494
  have hstable : (prefixWord ++ tailWord_999494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999494).length < 2 ^ (prefixWord ++ tailWord_999494).sum := by decide
  have hdescent : baseEnd_999494 < baseStart_999494 := by decide
  rcases family_descends (prefixWord ++ tailWord_999494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999503 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_999503 : Nat := 118140960795 + 999503 * 2 ^ 59
def prefixEnd_999503 : Nat := 4983230072969 + 3 ^ 40 * 999503 * 2
def baseEnd_999503 : Nat := 513225454610908173615875

theorem tailTrace_999503 : CollatzResearch.WordTrace tailWord_999503 prefixEnd_999503 513225454610908173615875 := by
  unfold tailWord_999503
  simp only [CollatzResearch.WordTrace]
  refine ⟨36454869297978807367267163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24303246198652538244844775 36454869297978807367267163)
  ·
    refine ⟨54682303946968211050900745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36454869297978807367267163 54682303946968211050900745)
    ·
      refine ⟨41011727960226158288175559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54682303946968211050900745 41011727960226158288175559)
      ·
        refine ⟨61517591940339237432263339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41011727960226158288175559 61517591940339237432263339)
        ·
          refine ⟨92276387910508856148395009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61517591940339237432263339 92276387910508856148395009)
          ·
            refine ⟨69207290932881642111296257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92276387910508856148395009 69207290932881642111296257)
            ·
              refine ⟨51905468199661231583472193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69207290932881642111296257 51905468199661231583472193)
              ·
                refine ⟨38929101149745923687604145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51905468199661231583472193 38929101149745923687604145)
                ·
                  refine ⟨29196825862309442765703109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38929101149745923687604145 29196825862309442765703109)
                  ·
                    refine ⟨5474404849183020518569333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29196825862309442765703109 5474404849183020518569333)
                    ·
                      refine ⟨513225454610908173615875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5474404849183020518569333 513225454610908173615875)
                      ·
                        rfl

theorem cell23_999503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_999503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999503 prefixEnd_999503 := by exact prefixLift 999503
  have htrace : WordTrace (prefixWord ++ tailWord_999503) baseStart_999503 baseEnd_999503 := by
    simpa [prefixWord, tailWord_999503, baseEnd_999503] using wordTrace_append hprefix tailTrace_999503
  have hstable : (prefixWord ++ tailWord_999503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999503).length < 2 ^ (prefixWord ++ tailWord_999503).sum := by decide
  have hdescent : baseEnd_999503 < baseStart_999503 := by decide
  rcases family_descends (prefixWord ++ tailWord_999503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999527 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 1, 5]
def baseStart_999527 : Nat := 118140960795 + 999527 * 2 ^ 59
def prefixEnd_999527 : Nat := 4983230072969 + 3 ^ 40 * 999527 * 2
def baseEnd_999527 : Nat := 171079259382205359905255

theorem tailTrace_999527 : CollatzResearch.WordTrace tailWord_999527 prefixEnd_999527 171079259382205359905255 := by
  unfold tailWord_999527
  simp only [CollatzResearch.WordTrace]
  refine ⟨36455744649891859466140835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24303829766594572977427223 36455744649891859466140835)
  ·
    refine ⟨54683616974837789199211253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36455744649891859466140835 54683616974837789199211253)
    ·
      refine ⟨5126589091391042737426055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54683616974837789199211253 5126589091391042737426055)
      ·
        refine ⟨7689883637086564106139083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126589091391042737426055 7689883637086564106139083)
        ·
          refine ⟨11534825455629846159208625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689883637086564106139083 11534825455629846159208625)
          ·
            refine ⟨8651119091722384619406469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11534825455629846159208625 8651119091722384619406469)
            ·
              refine ⟨1622084829697947116138713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8651119091722384619406469 1622084829697947116138713)
              ·
                refine ⟨1216563622273460337104035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622084829697947116138713 1216563622273460337104035)
                ·
                  refine ⟨1824845433410190505656053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216563622273460337104035 1824845433410190505656053)
                  ·
                    refine ⟨171079259382205359905255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1824845433410190505656053 171079259382205359905255)
                    ·
                      rfl

theorem cell23_999527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_999527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999527 prefixEnd_999527 := by exact prefixLift 999527
  have htrace : WordTrace (prefixWord ++ tailWord_999527) baseStart_999527 baseEnd_999527 := by
    simpa [prefixWord, tailWord_999527, baseEnd_999527] using wordTrace_append hprefix tailTrace_999527
  have hstable : (prefixWord ++ tailWord_999527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999527).length < 2 ^ (prefixWord ++ tailWord_999527).sum := by decide
  have hdescent : baseEnd_999527 < baseStart_999527 := by decide
  rcases family_descends (prefixWord ++ tailWord_999527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999534 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_999534 : Nat := 118140960795 + 999534 * 2 ^ 59
def prefixEnd_999534 : Nat := 4983230072969 + 3 ^ 40 * 999534 * 2
def baseEnd_999534 : Nat := 513241372511197552328233

theorem tailTrace_999534 : CollatzResearch.WordTrace tailWord_999534 prefixEnd_999534 513241372511197552328233 := by
  unfold tailWord_999534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4556999995108312457705707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24303999973910999774430437 4556999995108312457705707)
  ·
    refine ⟨6835499992662468686558561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4556999995108312457705707 6835499992662468686558561)
    ·
      refine ⟨5126624994496851514918921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6835499992662468686558561 5126624994496851514918921)
      ·
        refine ⟨3844968745872638636189191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5126624994496851514918921 3844968745872638636189191)
        ·
          refine ⟨5767453118808957954283787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844968745872638636189191 5767453118808957954283787)
          ·
            refine ⟨8651179678213436931425681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767453118808957954283787 8651179678213436931425681)
            ·
              refine ⟨6488384758660077698569261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8651179678213436931425681 6488384758660077698569261)
              ·
                refine ⟨2433144284497529136963473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6488384758660077698569261 2433144284497529136963473)
                ·
                  refine ⟨1824858213373146852722605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2433144284497529136963473 1824858213373146852722605)
                  ·
                    refine ⟨684321830014930069770977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1824858213373146852722605 684321830014930069770977)
                    ·
                      refine ⟨513241372511197552328233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 684321830014930069770977 513241372511197552328233)
                      ·
                        rfl

theorem cell23_999534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_999534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999534 prefixEnd_999534 := by exact prefixLift 999534
  have htrace : WordTrace (prefixWord ++ tailWord_999534) baseStart_999534 baseEnd_999534 := by
    simpa [prefixWord, tailWord_999534, baseEnd_999534] using wordTrace_append hprefix tailTrace_999534
  have hstable : (prefixWord ++ tailWord_999534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999534).length < 2 ^ (prefixWord ++ tailWord_999534).sum := by decide
  have hdescent : baseEnd_999534 < baseStart_999534 := by decide
  rcases family_descends (prefixWord ++ tailWord_999534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999557 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_999557 : Nat := 118140960795 + 999557 * 2 ^ 59
def prefixEnd_999557 : Nat := 4983230072969 + 3 ^ 40 * 999557 * 2
def baseEnd_999557 : Nat := 171084394188750320780209

theorem tailTrace_999557 : CollatzResearch.WordTrace tailWord_999557 prefixEnd_999557 171084394188750320780209 := by
  unfold tailWord_999557
  simp only [CollatzResearch.WordTrace]
  refine ⟨36456838839783174589732925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24304559226522116393155283 36456838839783174589732925)
  ·
    refine ⟨13671314564918690471149847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36456838839783174589732925 13671314564918690471149847)
    ·
      refine ⟨20506971847378035706724771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13671314564918690471149847 20506971847378035706724771)
      ·
        refine ⟨30760457771067053560087157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20506971847378035706724771 30760457771067053560087157)
        ·
          refine ⟨2883792916037536271258171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30760457771067053560087157 2883792916037536271258171)
          ·
            refine ⟨4325689374056304406887257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883792916037536271258171 4325689374056304406887257)
            ·
              refine ⟨3244267030542228305165443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325689374056304406887257 3244267030542228305165443)
              ·
                refine ⟨4866400545813342457748165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3244267030542228305165443 4866400545813342457748165)
                ·
                  refine ⟨912450102340001710827781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4866400545813342457748165 912450102340001710827781)
                  ·
                    refine ⟨171084394188750320780209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 912450102340001710827781 171084394188750320780209)
                    ·
                      rfl

theorem cell23_999557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_999557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999557 prefixEnd_999557 := by exact prefixLift 999557
  have htrace : WordTrace (prefixWord ++ tailWord_999557) baseStart_999557 baseEnd_999557 := by
    simpa [prefixWord, tailWord_999557, baseEnd_999557] using wordTrace_append hprefix tailTrace_999557
  have hstable : (prefixWord ++ tailWord_999557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999557).length < 2 ^ (prefixWord ++ tailWord_999557).sum := by decide
  have hdescent : baseEnd_999557 < baseStart_999557 := by decide
  rcases family_descends (prefixWord ++ tailWord_999557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999584 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 3]
def baseStart_999584 : Nat := 118140960795 + 999584 * 2 ^ 59
def prefixEnd_999584 : Nat := 4983230072969 + 3 ^ 40 * 999584 * 2
def baseEnd_999584 : Nat := 513267046543922356703003

theorem tailTrace_999584 : CollatzResearch.WordTrace tailWord_999584 prefixEnd_999584 513267046543922356703003 := by
  unfold tailWord_999584
  simp only [CollatzResearch.WordTrace]
  refine ⟨18228911805342679100482903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24305215740456905467310537 18228911805342679100482903)
  ·
    refine ⟨27343367708014018650724355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18228911805342679100482903 27343367708014018650724355)
    ·
      refine ⟨41015051562021027976086533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27343367708014018650724355 41015051562021027976086533)
      ·
        refine ⟨7690322167878942745516225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41015051562021027976086533 7690322167878942745516225)
        ·
          refine ⟨5767741625909207059137169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7690322167878942745516225 5767741625909207059137169)
          ·
            refine ⟨4325806219431905294352877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5767741625909207059137169 4325806219431905294352877)
            ·
              refine ⟨1622177332286964485382329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4325806219431905294352877 1622177332286964485382329)
              ·
                refine ⟨1216632999215223364036747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622177332286964485382329 1216632999215223364036747)
                ·
                  refine ⟨1824949498822835046055121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216632999215223364036747 1824949498822835046055121)
                  ·
                    refine ⟨1368712124117126284541341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1824949498822835046055121 1368712124117126284541341)
                    ·
                      refine ⟨513267046543922356703003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1368712124117126284541341 513267046543922356703003)
                      ·
                        rfl

theorem cell23_999584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_999584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999584 prefixEnd_999584 := by exact prefixLift 999584
  have htrace : WordTrace (prefixWord ++ tailWord_999584) baseStart_999584 baseEnd_999584 := by
    simpa [prefixWord, tailWord_999584, baseEnd_999584] using wordTrace_append hprefix tailTrace_999584
  have hstable : (prefixWord ++ tailWord_999584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999584).length < 2 ^ (prefixWord ++ tailWord_999584).sum := by decide
  have hdescent : baseEnd_999584 < baseStart_999584 := by decide
  rcases family_descends (prefixWord ++ tailWord_999584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999601 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 1, 1, 5]
def baseStart_999601 : Nat := 118140960795 + 999601 * 2 ^ 59
def prefixEnd_999601 : Nat := 4983230072969 + 3 ^ 40 * 999601 * 2
def baseEnd_999601 : Nat := 513275775715048790190425

theorem tailTrace_999601 : CollatzResearch.WordTrace tailWord_999601 prefixEnd_999601 513275775715048790190425 := by
  unfold tailWord_999601
  simp only [CollatzResearch.WordTrace]
  refine ⟨36458443651623770104334657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24305629101082513402889771 36458443651623770104334657)
  ·
    refine ⟨27343832738717827578250993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36458443651623770104334657 27343832738717827578250993)
    ·
      refine ⟨20507874554038370683688245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27343832738717827578250993 20507874554038370683688245)
      ·
        refine ⟨1922613239441097251595773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20507874554038370683688245 1922613239441097251595773)
        ·
          refine ⟨720979964790411469348415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1922613239441097251595773 720979964790411469348415)
          ·
            refine ⟨1081469947185617204022623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720979964790411469348415 1081469947185617204022623)
            ·
              refine ⟨1622204920778425806033935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081469947185617204022623 1622204920778425806033935)
              ·
                refine ⟨2433307381167638709050903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622204920778425806033935 2433307381167638709050903)
                ·
                  refine ⟨3649961071751458063576355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433307381167638709050903 3649961071751458063576355)
                  ·
                    refine ⟨5474941607627187095364533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3649961071751458063576355 5474941607627187095364533)
                    ·
                      refine ⟨513275775715048790190425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5474941607627187095364533 513275775715048790190425)
                      ·
                        rfl

theorem cell23_999601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_999601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999601 prefixEnd_999601 := by exact prefixLift 999601
  have htrace : WordTrace (prefixWord ++ tailWord_999601) baseStart_999601 baseEnd_999601 := by
    simpa [prefixWord, tailWord_999601, baseEnd_999601] using wordTrace_append hprefix tailTrace_999601
  have hstable : (prefixWord ++ tailWord_999601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999601).length < 2 ^ (prefixWord ++ tailWord_999601).sum := by decide
  have hdescent : baseEnd_999601 < baseStart_999601 := by decide
  rcases family_descends (prefixWord ++ tailWord_999601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999604 : List Nat := [2, 5, 3, 1, 12]
def baseStart_999604 : Nat := 118140960795 + 999604 * 2 ^ 59
def prefixEnd_999604 : Nat := 4983230072969 + 3 ^ 40 * 999604 * 2
def baseEnd_999604 : Nat := 704084109954749353159

theorem tailTrace_999604 : CollatzResearch.WordTrace tailWord_999604 prefixEnd_999604 704084109954749353159 := by
  unfold tailWord_999604
  simp only [CollatzResearch.WordTrace]
  refine ⟨18229276535306450808346933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24305702047075267744462577 18229276535306450808346933)
  ·
    refine ⟨1708994675184979763282525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18229276535306450808346933 1708994675184979763282525)
    ·
      refine ⟨640873003194367411230947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1708994675184979763282525 640873003194367411230947)
      ·
        refine ⟨961309504791551116846421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640873003194367411230947 961309504791551116846421)
        ·
          refine ⟨704084109954749353159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 961309504791551116846421 704084109954749353159)
          ·
            rfl

theorem cell23_999604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 12].length) (baseStart_999604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999604 prefixEnd_999604 := by exact prefixLift 999604
  have htrace : WordTrace (prefixWord ++ tailWord_999604) baseStart_999604 baseEnd_999604 := by
    simpa [prefixWord, tailWord_999604, baseEnd_999604] using wordTrace_append hprefix tailTrace_999604
  have hstable : (prefixWord ++ tailWord_999604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999604).length < 2 ^ (prefixWord ++ tailWord_999604).sum := by decide
  have hdescent : baseEnd_999604 < baseStart_999604 := by decide
  rcases family_descends (prefixWord ++ tailWord_999604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999610 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_999610 : Nat := 118140960795 + 999610 * 2 ^ 59
def prefixEnd_999610 : Nat := 4983230072969 + 3 ^ 40 * 999610 * 2
def baseEnd_999610 : Nat := 513280397040939254977883

theorem tailTrace_999610 : CollatzResearch.WordTrace tailWord_999610 prefixEnd_999610 513280397040939254977883 := by
  unfold tailWord_999610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9114692977147791160353071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24305847939060776427608189 9114692977147791160353071)
  ·
    refine ⟨13672039465721686740529607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9114692977147791160353071 13672039465721686740529607)
    ·
      refine ⟨20508059198582530110794411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13672039465721686740529607 20508059198582530110794411)
      ·
        refine ⟨30762088797873795166191617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20508059198582530110794411 30762088797873795166191617)
        ·
          refine ⟨23071566598405346374643713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30762088797873795166191617 23071566598405346374643713)
          ·
            refine ⟨17303674948804009780982785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23071566598405346374643713 17303674948804009780982785)
            ·
              refine ⟨12977756211603007335737089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17303674948804009780982785 12977756211603007335737089)
              ·
                refine ⟨9733317158702255501802817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12977756211603007335737089 9733317158702255501802817)
                ·
                  refine ⟨7299987869026691626352113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9733317158702255501802817 7299987869026691626352113)
                  ·
                    refine ⟨5474990901770018719764085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7299987869026691626352113 5474990901770018719764085)
                    ·
                      refine ⟨513280397040939254977883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5474990901770018719764085 513280397040939254977883)
                      ·
                        rfl

theorem cell23_999610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_999610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999610 prefixEnd_999610 := by exact prefixLift 999610
  have htrace : WordTrace (prefixWord ++ tailWord_999610) baseStart_999610 baseEnd_999610 := by
    simpa [prefixWord, tailWord_999610, baseEnd_999610] using wordTrace_append hprefix tailTrace_999610
  have hstable : (prefixWord ++ tailWord_999610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999610).length < 2 ^ (prefixWord ++ tailWord_999610).sum := by decide
  have hdescent : baseEnd_999610 < baseStart_999610 := by decide
  rcases family_descends (prefixWord ++ tailWord_999610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999660 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 9]
def baseStart_999660 : Nat := 118140960795 + 999660 * 2 ^ 59
def prefixEnd_999660 : Nat := 4983230072969 + 3 ^ 40 * 999660 * 2
def baseEnd_999660 : Nat := 57034007897073784372517

theorem tailTrace_999660 : CollatzResearch.WordTrace tailWord_999660 prefixEnd_999660 57034007897073784372517 := by
  unfold tailWord_999660
  simp only [CollatzResearch.WordTrace]
  refine ⟨18230297779205011590366217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24307063705606682120488289 18230297779205011590366217)
  ·
    refine ⟨13672723334403758692774663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18230297779205011590366217 13672723334403758692774663)
    ·
      refine ⟨20509085001605638039161995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13672723334403758692774663 20509085001605638039161995)
      ·
        refine ⟨30763627502408457058742993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20509085001605638039161995 30763627502408457058742993)
        ·
          refine ⟨23072720626806342794057245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30763627502408457058742993 23072720626806342794057245)
          ·
            refine ⟨8652270235052378547771467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23072720626806342794057245 8652270235052378547771467)
            ·
              refine ⟨12978405352578567821657201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652270235052378547771467 12978405352578567821657201)
              ·
                refine ⟨9733804014433925866242901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12978405352578567821657201 9733804014433925866242901)
                ·
                  refine ⟨57034007897073784372517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9733804014433925866242901 57034007897073784372517)
                  ·
                    rfl

theorem cell23_999660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_999660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999660 prefixEnd_999660 := by exact prefixLift 999660
  have htrace : WordTrace (prefixWord ++ tailWord_999660) baseStart_999660 baseEnd_999660 := by
    simpa [prefixWord, tailWord_999660, baseEnd_999660] using wordTrace_append hprefix tailTrace_999660
  have hstable : (prefixWord ++ tailWord_999660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999660).length < 2 ^ (prefixWord ++ tailWord_999660).sum := by decide
  have hdescent : baseEnd_999660 < baseStart_999660 := by decide
  rcases family_descends (prefixWord ++ tailWord_999660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999711 : List Nat := [1, 1, 2, 4, 3, 3, 1, 3, 5]
def baseStart_999711 : Nat := 118140960795 + 999711 * 2 ^ 59
def prefixEnd_999711 : Nat := 4983230072969 + 3 ^ 40 * 999711 * 2
def baseEnd_999711 : Nat := 57036917620782595534991

theorem tailTrace_999711 : CollatzResearch.WordTrace tailWord_999711 prefixEnd_999711 57036917620782595534991 := by
  unfold tailWord_999711
  simp only [CollatzResearch.WordTrace]
  refine ⟨36462455681225258890838987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24308303787483505927225991 36462455681225258890838987)
  ·
    refine ⟨54693683521837888336258481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36462455681225258890838987 54693683521837888336258481)
    ·
      refine ⟨41020262641378416252193861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54693683521837888336258481 41020262641378416252193861)
      ·
        refine ⟨7691299245258453047286349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41020262641378416252193861 7691299245258453047286349)
        ·
          refine ⟨2884237216971919892732381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7691299245258453047286349 2884237216971919892732381)
          ·
            refine ⟨1081588956364469959774643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2884237216971919892732381 1081588956364469959774643)
            ·
              refine ⟨1622383434546704939661965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081588956364469959774643 1622383434546704939661965)
              ·
                refine ⟨608393787955014352373237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1622383434546704939661965 608393787955014352373237)
                ·
                  refine ⟨57036917620782595534991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 608393787955014352373237 57036917620782595534991)
                  ·
                    rfl

theorem cell23_999711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 5].length) (baseStart_999711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999711 prefixEnd_999711 := by exact prefixLift 999711
  have htrace : WordTrace (prefixWord ++ tailWord_999711) baseStart_999711 baseEnd_999711 := by
    simpa [prefixWord, tailWord_999711, baseEnd_999711] using wordTrace_append hprefix tailTrace_999711
  have hstable : (prefixWord ++ tailWord_999711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999711).length < 2 ^ (prefixWord ++ tailWord_999711).sum := by decide
  have hdescent : baseEnd_999711 < baseStart_999711 := by decide
  rcases family_descends (prefixWord ++ tailWord_999711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999727 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_999727 : Nat := 118140960795 + 999727 * 2 ^ 59
def prefixEnd_999727 : Nat := 4983230072969 + 3 ^ 40 * 999727 * 2
def baseEnd_999727 : Nat := 513340474277515297214845

theorem tailTrace_999727 : CollatzResearch.WordTrace tailWord_999727 prefixEnd_999727 513340474277515297214845 := by
  unfold tailWord_999727
  simp only [CollatzResearch.WordTrace]
  refine ⟨36463039249167293623421435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24308692832778195748947623 36463039249167293623421435)
  ·
    refine ⟨54694558873750940435132153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36463039249167293623421435 54694558873750940435132153)
    ·
      refine ⟨41020919155313205326349115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54694558873750940435132153 41020919155313205326349115)
      ·
        refine ⟨61531378732969807989523673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41020919155313205326349115 61531378732969807989523673)
        ·
          refine ⟨46148534049727355992142755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61531378732969807989523673 46148534049727355992142755)
          ·
            refine ⟨69222801074591033988214133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46148534049727355992142755 69222801074591033988214133)
            ·
              refine ⟨6489637600742909436395075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69222801074591033988214133 6489637600742909436395075)
              ·
                refine ⟨9734456401114364154592613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6489637600742909436395075 9734456401114364154592613)
                ·
                  refine ⟨1825210575208943278986115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9734456401114364154592613 1825210575208943278986115)
                  ·
                    refine ⟨2737815862813414918479173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1825210575208943278986115 2737815862813414918479173)
                    ·
                      refine ⟨513340474277515297214845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2737815862813414918479173 513340474277515297214845)
                      ·
                        rfl

theorem cell23_999727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_999727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999727 prefixEnd_999727 := by exact prefixLift 999727
  have htrace : WordTrace (prefixWord ++ tailWord_999727) baseStart_999727 baseEnd_999727 := by
    simpa [prefixWord, tailWord_999727, baseEnd_999727] using wordTrace_append hprefix tailTrace_999727
  have hstable : (prefixWord ++ tailWord_999727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999727).length < 2 ^ (prefixWord ++ tailWord_999727).sum := by decide
  have hdescent : baseEnd_999727 < baseStart_999727 := by decide
  rcases family_descends (prefixWord ++ tailWord_999727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
