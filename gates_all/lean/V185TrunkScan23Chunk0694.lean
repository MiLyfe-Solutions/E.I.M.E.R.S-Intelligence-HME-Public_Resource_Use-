import V185TrunkScan23Chunk0693

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4103279 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_4103279 : Nat := 118140960795 + 4103279 * 2 ^ 59
def prefixEnd_4103279 : Nat := 4983230072969 + 3 ^ 40 * 4103279 * 2
def baseEnd_4103279 : Nat := 2106954386500156635741869

theorem tailTrace_4103279 : CollatzResearch.WordTrace tailWord_4103279 prefixEnd_4103279 2106954386500156635741869 := by
  unfold tailWord_4103279
  simp only [CollatzResearch.WordTrace]
  refine ⟨149658880101528442106024891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99772586734352294737349927 149658880101528442106024891)
  ·
    refine ⟨224488320152292663159037337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149658880101528442106024891 224488320152292663159037337)
    ·
      refine ⟨168366240114219497369278003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224488320152292663159037337 168366240114219497369278003)
      ·
        refine ⟨252549360171329246053917005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168366240114219497369278003 252549360171329246053917005)
        ·
          refine ⟨94706010064248467270218877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252549360171329246053917005 94706010064248467270218877)
          ·
            refine ⟨35514753774093175226332079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94706010064248467270218877 35514753774093175226332079)
            ·
              refine ⟨53272130661139762839498119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35514753774093175226332079 53272130661139762839498119)
              ·
                refine ⟨79908195991709644259247179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53272130661139762839498119 79908195991709644259247179)
                ·
                  refine ⟨119862293987564466388870769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79908195991709644259247179 119862293987564466388870769)
                  ·
                    refine ⟨89896720490673349791653077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119862293987564466388870769 89896720490673349791653077)
                    ·
                      refine ⟨2106954386500156635741869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89896720490673349791653077 2106954386500156635741869)
                      ·
                        rfl

theorem cell23_4103279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_4103279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103279 prefixEnd_4103279 := by exact prefixLift 4103279
  have htrace : WordTrace (prefixWord ++ tailWord_4103279) baseStart_4103279 baseEnd_4103279 := by
    simpa [prefixWord, tailWord_4103279, baseEnd_4103279] using wordTrace_append hprefix tailTrace_4103279
  have hstable : (prefixWord ++ tailWord_4103279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103279).length < 2 ^ (prefixWord ++ tailWord_4103279).sum := by decide
  have hdescent : baseEnd_4103279 < baseStart_4103279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103280 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 2, 2, 2]
def baseStart_4103280 : Nat := 118140960795 + 4103280 * 2 ^ 59
def prefixEnd_4103280 : Nat := 4983230072969 + 3 ^ 40 * 4103280 * 2
def baseEnd_4103280 : Nat := 2106954899980811131829365

theorem tailTrace_4103280 : CollatzResearch.WordTrace tailWord_4103280 prefixEnd_4103280 2106954899980811131829365 := by
  unfold tailWord_4103280
  simp only [CollatzResearch.WordTrace]
  refine ⟨74829458287262409638405647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99772611049683212851207529 74829458287262409638405647)
  ·
    refine ⟨112244187430893614457608471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74829458287262409638405647 112244187430893614457608471)
    ·
      refine ⟨168366281146340421686412707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112244187430893614457608471 168366281146340421686412707)
      ·
        refine ⟨252549421719510632529619061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168366281146340421686412707 252549421719510632529619061)
        ·
          refine ⟨23676508286204121799651787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252549421719510632529619061 23676508286204121799651787)
          ·
            refine ⟨35514762429306182699477681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23676508286204121799651787 35514762429306182699477681)
            ·
              refine ⟨26636071821979637024608261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35514762429306182699477681 26636071821979637024608261)
              ·
                refine ⟨4994263466621181942114049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26636071821979637024608261 4994263466621181942114049)
                ·
                  refine ⟨3745697599965886456585537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994263466621181942114049 3745697599965886456585537)
                  ·
                    refine ⟨2809273199974414842439153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3745697599965886456585537 2809273199974414842439153)
                    ·
                      refine ⟨2106954899980811131829365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809273199974414842439153 2106954899980811131829365)
                      ·
                        rfl

theorem cell23_4103280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 2, 2].length) (baseStart_4103280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103280 prefixEnd_4103280 := by exact prefixLift 4103280
  have htrace : WordTrace (prefixWord ++ tailWord_4103280) baseStart_4103280 baseEnd_4103280 := by
    simpa [prefixWord, tailWord_4103280, baseEnd_4103280] using wordTrace_append hprefix tailTrace_4103280
  have hstable : (prefixWord ++ tailWord_4103280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103280).length < 2 ^ (prefixWord ++ tailWord_4103280).sum := by decide
  have hdescent : baseEnd_4103280 < baseStart_4103280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103296 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 3]
def baseStart_4103296 : Nat := 118140960795 + 4103296 * 2 ^ 59
def prefixEnd_4103296 : Nat := 4983230072969 + 3 ^ 40 * 4103296 * 2
def baseEnd_4103296 : Nat := 2106963115671283069229291

theorem tailTrace_4103296 : CollatzResearch.WordTrace tailWord_4103296 prefixEnd_4103296 2106963115671283069229291 := by
  unfold tailWord_4103296
  simp only [CollatzResearch.WordTrace]
  refine ⟨74829750071233427004696871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99773000094977902672929161 74829750071233427004696871)
  ·
    refine ⟨112244625106850140507045307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74829750071233427004696871 112244625106850140507045307)
    ·
      refine ⟨168366937660275210760567961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112244625106850140507045307 168366937660275210760567961)
      ·
        refine ⟨126275203245206408070425971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168366937660275210760567961 126275203245206408070425971)
        ·
          refine ⟨189412804867809612105638957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126275203245206408070425971 189412804867809612105638957)
          ·
            refine ⟨71029801825428604539614609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189412804867809612105638957 71029801825428604539614609)
            ·
              refine ⟨53272351369071453404710957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71029801825428604539614609 53272351369071453404710957)
              ·
                refine ⟨19977131763401795026766609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53272351369071453404710957 19977131763401795026766609)
                ·
                  refine ⟨14982848822551346270074957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19977131763401795026766609 14982848822551346270074957)
                  ·
                    refine ⟨5618568308456754851278109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14982848822551346270074957 5618568308456754851278109)
                    ·
                      refine ⟨2106963115671283069229291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5618568308456754851278109 2106963115671283069229291)
                      ·
                        rfl

theorem cell23_4103296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_4103296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103296 prefixEnd_4103296 := by exact prefixLift 4103296
  have htrace : WordTrace (prefixWord ++ tailWord_4103296) baseStart_4103296 baseEnd_4103296 := by
    simpa [prefixWord, tailWord_4103296, baseEnd_4103296] using wordTrace_append hprefix tailTrace_4103296
  have hstable : (prefixWord ++ tailWord_4103296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103296).length < 2 ^ (prefixWord ++ tailWord_4103296).sum := by decide
  have hdescent : baseEnd_4103296 < baseStart_4103296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103297 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_4103297 : Nat := 118140960795 + 4103297 * 2 ^ 59
def prefixEnd_4103297 : Nat := 4983230072969 + 3 ^ 40 * 4103297 * 2
def baseEnd_4103297 : Nat := 2106963629151937565316787

theorem tailTrace_4103297 : CollatzResearch.WordTrace tailWord_4103297 prefixEnd_4103297 2106963629151937565316787 := by
  unfold tailWord_4103297
  simp only [CollatzResearch.WordTrace]
  refine ⟨149659536615463231180180145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99773024410308820786786763 149659536615463231180180145)
  ·
    refine ⟨112244652461597423385135109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149659536615463231180180145 112244652461597423385135109)
    ·
      refine ⟨21045872336549516884712833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112244652461597423385135109 21045872336549516884712833)
      ·
        refine ⟨15784404252412137663534625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21045872336549516884712833 15784404252412137663534625)
        ·
          refine ⟨11838303189309103247650969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15784404252412137663534625 11838303189309103247650969)
          ·
            refine ⟨8878727391981827435738227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11838303189309103247650969 8878727391981827435738227)
            ·
              refine ⟨13318091087972741153607341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8878727391981827435738227 13318091087972741153607341)
              ·
                refine ⟨4994284157989777932602753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13318091087972741153607341 4994284157989777932602753)
                ·
                  refine ⟨3745713118492333449452065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994284157989777932602753 3745713118492333449452065)
                  ·
                    refine ⟨2809284838869250087089049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3745713118492333449452065 2809284838869250087089049)
                    ·
                      refine ⟨2106963629151937565316787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809284838869250087089049 2106963629151937565316787)
                      ·
                        rfl

theorem cell23_4103297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_4103297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103297 prefixEnd_4103297 := by exact prefixLift 4103297
  have htrace : WordTrace (prefixWord ++ tailWord_4103297) baseStart_4103297 baseEnd_4103297 := by
    simpa [prefixWord, tailWord_4103297, baseEnd_4103297] using wordTrace_append hprefix tailTrace_4103297
  have hstable : (prefixWord ++ tailWord_4103297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103297).length < 2 ^ (prefixWord ++ tailWord_4103297).sum := by decide
  have hdescent : baseEnd_4103297 < baseStart_4103297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103353 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 1, 6, 2]
def baseStart_4103353 : Nat := 118140960795 + 4103353 * 2 ^ 59
def prefixEnd_4103353 : Nat := 4983230072969 + 3 ^ 40 * 4103353 * 2
def baseEnd_4103353 : Nat := 2106992384068589346216529

theorem tailTrace_4103353 : CollatzResearch.WordTrace tailWord_4103353 prefixEnd_4103353 2106992384068589346216529 := by
  unfold tailWord_4103353
  simp only [CollatzResearch.WordTrace]
  refine ⟨149661579103260352744218713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99774386068840235162812475 149661579103260352744218713)
  ·
    refine ⟨112246184327445264558164035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149661579103260352744218713 112246184327445264558164035)
    ·
      refine ⟨168369276491167896837246053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112246184327445264558164035 168369276491167896837246053)
      ·
        refine ⟨31569239342093980656983635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168369276491167896837246053 31569239342093980656983635)
        ·
          refine ⟨47353859013140970985475453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31569239342093980656983635 47353859013140970985475453)
          ·
            refine ⟨17757697129927864119553295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47353859013140970985475453 17757697129927864119553295)
            ·
              refine ⟨26636545694891796179329943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17757697129927864119553295 26636545694891796179329943)
              ·
                refine ⟨39954818542337694268994915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26636545694891796179329943 39954818542337694268994915)
                ·
                  refine ⟨59932227813506541403492373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39954818542337694268994915 59932227813506541403492373)
                  ·
                    refine ⟨2809323178758119128288705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59932227813506541403492373 2809323178758119128288705)
                    ·
                      refine ⟨2106992384068589346216529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809323178758119128288705 2106992384068589346216529)
                      ·
                        rfl

theorem cell23_4103353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_4103353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103353 prefixEnd_4103353 := by exact prefixLift 4103353
  have htrace : WordTrace (prefixWord ++ tailWord_4103353) baseStart_4103353 baseEnd_4103353 := by
    simpa [prefixWord, tailWord_4103353, baseEnd_4103353] using wordTrace_append hprefix tailTrace_4103353
  have hstable : (prefixWord ++ tailWord_4103353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103353).length < 2 ^ (prefixWord ++ tailWord_4103353).sum := by decide
  have hdescent : baseEnd_4103353 < baseStart_4103353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103370 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_4103370 : Nat := 118140960795 + 4103370 * 2 ^ 59
def prefixEnd_4103370 : Nat := 4983230072969 + 3 ^ 40 * 4103370 * 2
def baseEnd_4103370 : Nat := 2107001113239715779703951

theorem tailTrace_4103370 : CollatzResearch.WordTrace tailWord_4103370 prefixEnd_4103370 2107001113239715779703951 := by
  unfold tailWord_4103370
  simp only [CollatzResearch.WordTrace]
  refine ⟨37415549786049691161896891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99774799429465843098391709 37415549786049691161896891)
  ·
    refine ⟨56123324679074536742845337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37415549786049691161896891 56123324679074536742845337)
    ·
      refine ⟨42092493509305902557134003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56123324679074536742845337 42092493509305902557134003)
      ·
        refine ⟨63138740263958853835701005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42092493509305902557134003 63138740263958853835701005)
        ·
          refine ⟨23677027598984570188387877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63138740263958853835701005 23677027598984570188387877)
          ·
            refine ⟨4439442674809606910322727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23677027598984570188387877 4439442674809606910322727)
            ·
              refine ⟨6659164012214410365484091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439442674809606910322727 6659164012214410365484091)
              ·
                refine ⟨9988746018321615548226137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659164012214410365484091 9988746018321615548226137)
                ·
                  refine ⟨7491559513741211661169603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9988746018321615548226137 7491559513741211661169603)
                  ·
                    refine ⟨11237339270611817491754405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7491559513741211661169603 11237339270611817491754405)
                    ·
                      refine ⟨2107001113239715779703951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11237339270611817491754405 2107001113239715779703951)
                      ·
                        rfl

theorem cell23_4103370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_4103370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103370 prefixEnd_4103370 := by exact prefixLift 4103370
  have htrace : WordTrace (prefixWord ++ tailWord_4103370) baseStart_4103370 baseEnd_4103370 := by
    simpa [prefixWord, tailWord_4103370, baseEnd_4103370] using wordTrace_append hprefix tailTrace_4103370
  have hstable : (prefixWord ++ tailWord_4103370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103370).length < 2 ^ (prefixWord ++ tailWord_4103370).sum := by decide
  have hdescent : baseEnd_4103370 < baseStart_4103370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103393 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 6]
def baseStart_4103393 : Nat := 118140960795 + 4103393 * 2 ^ 59
def prefixEnd_4103393 : Nat := 4983230072969 + 3 ^ 40 * 4103393 * 2
def baseEnd_4103393 : Nat := 234112547032752132190705

theorem tailTrace_4103393 : CollatzResearch.WordTrace tailWord_4103393 prefixEnd_4103393 234112547032752132190705 := by
  unfold tailWord_4103393
  simp only [CollatzResearch.WordTrace]
  refine ⟨149663038023115439575674833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99775358682076959717116555 149663038023115439575674833)
  ·
    refine ⟨112247278517336579681756125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149663038023115439575674833 112247278517336579681756125)
    ·
      refine ⟨42092729444001217380658547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112247278517336579681756125 42092729444001217380658547)
      ·
        refine ⟨63139094166001826070987821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42092729444001217380658547 63139094166001826070987821)
        ·
          refine ⟨23677160312250684776620433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63139094166001826070987821 23677160312250684776620433)
          ·
            refine ⟨17757870234188013582465325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23677160312250684776620433 17757870234188013582465325)
            ·
              refine ⟨6659201337820505093424497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17757870234188013582465325 6659201337820505093424497)
              ·
                refine ⟨4994401003365378820068373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659201337820505093424497 4994401003365378820068373)
                ·
                  refine ⟨234112547032752132190705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4994401003365378820068373 234112547032752132190705)
                  ·
                    rfl

theorem cell23_4103393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 6].length) (baseStart_4103393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103393 prefixEnd_4103393 := by exact prefixLift 4103393
  have htrace : WordTrace (prefixWord ++ tailWord_4103393) baseStart_4103393 baseEnd_4103393 := by
    simpa [prefixWord, tailWord_4103393, baseEnd_4103393] using wordTrace_append hprefix tailTrace_4103393
  have hstable : (prefixWord ++ tailWord_4103393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103393).length < 2 ^ (prefixWord ++ tailWord_4103393).sum := by decide
  have hdescent : baseEnd_4103393 < baseStart_4103393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103396 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_4103396 : Nat := 118140960795 + 4103396 * 2 ^ 59
def prefixEnd_4103396 : Nat := 4983230072969 + 3 ^ 40 * 4103396 * 2
def baseEnd_4103396 : Nat := 2107014463736732677978831

theorem tailTrace_4103396 : CollatzResearch.WordTrace tailWord_4103396 prefixEnd_4103396 2107014463736732677978831 := by
  unfold tailWord_4103396
  simp only [CollatzResearch.WordTrace]
  refine ⟨74831573721052285544017021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99775431628069714058689361 74831573721052285544017021)
  ·
    refine ⟨28061840145394607079006383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74831573721052285544017021 28061840145394607079006383)
    ·
      refine ⟨42092760218091910618509575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28061840145394607079006383 42092760218091910618509575)
      ·
        refine ⟨63139140327137865927764363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42092760218091910618509575 63139140327137865927764363)
        ·
          refine ⟨94708710490706798891646545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63139140327137865927764363 94708710490706798891646545)
          ·
            refine ⟨71031532868030099168734909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94708710490706798891646545 71031532868030099168734909)
            ·
              refine ⟨26636824825511287188275591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71031532868030099168734909 26636824825511287188275591)
              ·
                refine ⟨39955237238266930782413387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26636824825511287188275591 39955237238266930782413387)
                ·
                  refine ⟨59932855857400396173620081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39955237238266930782413387 59932855857400396173620081)
                  ·
                    refine ⟨44949641893050297130215061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59932855857400396173620081 44949641893050297130215061)
                    ·
                      refine ⟨2107014463736732677978831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44949641893050297130215061 2107014463736732677978831)
                      ·
                        rfl

theorem cell23_4103396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_4103396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103396 prefixEnd_4103396 := by exact prefixLift 4103396
  have htrace : WordTrace (prefixWord ++ tailWord_4103396) baseStart_4103396 baseEnd_4103396 := by
    simpa [prefixWord, tailWord_4103396, baseEnd_4103396] using wordTrace_append hprefix tailTrace_4103396
  have hstable : (prefixWord ++ tailWord_4103396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103396).length < 2 ^ (prefixWord ++ tailWord_4103396).sum := by decide
  have hdescent : baseEnd_4103396 < baseStart_4103396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103423 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 1, 5]
def baseStart_4103423 : Nat := 118140960795 + 4103423 * 2 ^ 59
def prefixEnd_4103423 : Nat := 4983230072969 + 3 ^ 40 * 4103423 * 2
def baseEnd_4103423 : Nat := 702342775904801357447069

theorem tailTrace_4103423 : CollatzResearch.WordTrace tailWord_4103423 prefixEnd_4103423 702342775904801357447069 := by
  unfold tailWord_4103423
  simp only [CollatzResearch.WordTrace]
  refine ⟨149664132213006754699266923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99776088142004503132844615 149664132213006754699266923)
  ·
    refine ⟨224496198319510132048900385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149664132213006754699266923 224496198319510132048900385)
    ·
      refine ⟨168372148739632599036675289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224496198319510132048900385 168372148739632599036675289)
      ·
        refine ⟨126279111554724449277506467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168372148739632599036675289 126279111554724449277506467)
        ·
          refine ⟨189418667332086673916259701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126279111554724449277506467 189418667332086673916259701)
          ·
            refine ⟨17758000062383125679649347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189418667332086673916259701 17758000062383125679649347)
            ·
              refine ⟨26637000093574688519474021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17758000062383125679649347 26637000093574688519474021)
              ·
                refine ⟨4994437517545254097401379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26637000093574688519474021 4994437517545254097401379)
                ·
                  refine ⟨7491656276317881146102069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994437517545254097401379 7491656276317881146102069)
                  ·
                    refine ⟨702342775904801357447069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7491656276317881146102069 702342775904801357447069)
                    ·
                      rfl

theorem cell23_4103423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 5].length) (baseStart_4103423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103423 prefixEnd_4103423 := by exact prefixLift 4103423
  have htrace : WordTrace (prefixWord ++ tailWord_4103423) baseStart_4103423 baseEnd_4103423 := by
    simpa [prefixWord, tailWord_4103423, baseEnd_4103423] using wordTrace_append hprefix tailTrace_4103423
  have hstable : (prefixWord ++ tailWord_4103423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103423).length < 2 ^ (prefixWord ++ tailWord_4103423).sum := by decide
  have hdescent : baseEnd_4103423 < baseStart_4103423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103473 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_4103473 : Nat := 118140960795 + 4103473 * 2 ^ 59
def prefixEnd_4103473 : Nat := 4983230072969 + 3 ^ 40 * 4103473 * 2
def baseEnd_4103473 : Nat := 2107054001747128876715977

theorem tailTrace_4103473 : CollatzResearch.WordTrace tailWord_4103473 prefixEnd_4103473 2107054001747128876715977 := by
  unfold tailWord_4103473
  simp only [CollatzResearch.WordTrace]
  refine ⟨149665955862825613238587073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99777303908550408825724715 149665955862825613238587073)
  ·
    refine ⟨112249466897119209928940305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149665955862825613238587073 112249466897119209928940305)
    ·
      refine ⟨84187100172839407446705229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112249466897119209928940305 84187100172839407446705229)
      ·
        refine ⟨31570162564814777792514461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84187100172839407446705229 31570162564814777792514461)
        ·
          refine ⟨11838810961805541672192923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31570162564814777792514461 11838810961805541672192923)
          ·
            refine ⟨17758216442708312508289385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11838810961805541672192923 17758216442708312508289385)
            ·
              refine ⟨13318662332031234381217039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17758216442708312508289385 13318662332031234381217039)
              ·
                refine ⟨19977993498046851571825559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13318662332031234381217039 19977993498046851571825559)
                ·
                  refine ⟨29966990247070277357738339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19977993498046851571825559 29966990247070277357738339)
                  ·
                    refine ⟨44950485370605416036607509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29966990247070277357738339 44950485370605416036607509)
                    ·
                      refine ⟨2107054001747128876715977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44950485370605416036607509 2107054001747128876715977)
                      ·
                        rfl

theorem cell23_4103473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_4103473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103473 prefixEnd_4103473 := by exact prefixLift 4103473
  have htrace : WordTrace (prefixWord ++ tailWord_4103473) baseStart_4103473 baseEnd_4103473 := by
    simpa [prefixWord, tailWord_4103473, baseEnd_4103473] using wordTrace_append hprefix tailTrace_4103473
  have hstable : (prefixWord ++ tailWord_4103473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103473).length < 2 ^ (prefixWord ++ tailWord_4103473).sum := by decide
  have hdescent : baseEnd_4103473 < baseStart_4103473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103477 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_4103477 : Nat := 118140960795 + 4103477 * 2 ^ 59
def prefixEnd_4103477 : Nat := 4983230072969 + 3 ^ 40 * 4103477 * 2
def baseEnd_4103477 : Nat := 2107056055669746861065959

theorem tailTrace_4103477 : CollatzResearch.WordTrace tailWord_4103477 prefixEnd_4103477 2107056055669746861065959 := by
  unfold tailWord_4103477
  simp only [CollatzResearch.WordTrace]
  refine ⟨149666101754811121921732685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99777401169874081281155123 149666101754811121921732685)
  ·
    refine ⟨56124788158054170720649757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149666101754811121921732685 56124788158054170720649757)
    ·
      refine ⟨21046795559270314020243659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56124788158054170720649757 21046795559270314020243659)
      ·
        refine ⟨31570193338905471030365489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21046795559270314020243659 31570193338905471030365489)
        ·
          refine ⟨23677645004179103272774117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31570193338905471030365489 23677645004179103272774117)
          ·
            refine ⟨4439558438283581863645147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23677645004179103272774117 4439558438283581863645147)
            ·
              refine ⟨6659337657425372795467721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439558438283581863645147 6659337657425372795467721)
              ·
                refine ⟨4994503243069029596600791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659337657425372795467721 4994503243069029596600791)
                ·
                  refine ⟨7491754864603544394901187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994503243069029596600791 7491754864603544394901187)
                  ·
                    refine ⟨11237632296905316592351781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7491754864603544394901187 11237632296905316592351781)
                    ·
                      refine ⟨2107056055669746861065959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11237632296905316592351781 2107056055669746861065959)
                      ·
                        rfl

theorem cell23_4103477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_4103477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103477 prefixEnd_4103477 := by exact prefixLift 4103477
  have htrace : WordTrace (prefixWord ++ tailWord_4103477) baseStart_4103477 baseEnd_4103477 := by
    simpa [prefixWord, tailWord_4103477, baseEnd_4103477] using wordTrace_append hprefix tailTrace_4103477
  have hstable : (prefixWord ++ tailWord_4103477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103477).length < 2 ^ (prefixWord ++ tailWord_4103477).sum := by decide
  have hdescent : baseEnd_4103477 < baseStart_4103477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103511 : List Nat := [1, 1, 3, 2, 3, 2, 4, 2, 1, 2, 2]
def baseStart_4103511 : Nat := 118140960795 + 4103511 * 2 ^ 59
def prefixEnd_4103511 : Nat := 4983230072969 + 3 ^ 40 * 4103511 * 2
def baseEnd_4103511 : Nat := 2107073514011999728040803

theorem tailTrace_4103511 : CollatzResearch.WordTrace tailWord_4103511 prefixEnd_4103511 2107073514011999728040803 := by
  unfold tailWord_4103511
  simp only [CollatzResearch.WordTrace]
  refine ⟨149667341836687945728470387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99778227891125297152313591 149667341836687945728470387)
  ·
    refine ⟨224501012755031918592705581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149667341836687945728470387 224501012755031918592705581)
    ·
      refine ⟨84187879783136969472264593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224501012755031918592705581 84187879783136969472264593)
      ·
        refine ⟨63140909837352727104198445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84187879783136969472264593 63140909837352727104198445)
        ·
          refine ⟨23677841189007272664074417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63140909837352727104198445 23677841189007272664074417)
          ·
            refine ⟨17758380891755454498055813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23677841189007272664074417 17758380891755454498055813)
            ·
              refine ⟨3329696417204147718385465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17758380891755454498055813 3329696417204147718385465)
              ·
                refine ⟨2497272312903110788789099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3329696417204147718385465 2497272312903110788789099)
                ·
                  refine ⟨3745908469354666183183649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497272312903110788789099 3745908469354666183183649)
                  ·
                    refine ⟨2809431352015999637387737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3745908469354666183183649 2809431352015999637387737)
                    ·
                      refine ⟨2107073514011999728040803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809431352015999637387737 2107073514011999728040803)
                      ·
                        rfl

theorem cell23_4103511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_4103511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103511 prefixEnd_4103511 := by exact prefixLift 4103511
  have htrace : WordTrace (prefixWord ++ tailWord_4103511) baseStart_4103511 baseEnd_4103511 := by
    simpa [prefixWord, tailWord_4103511, baseEnd_4103511] using wordTrace_append hprefix tailTrace_4103511
  have hstable : (prefixWord ++ tailWord_4103511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103511).length < 2 ^ (prefixWord ++ tailWord_4103511).sum := by decide
  have hdescent : baseEnd_4103511 < baseStart_4103511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103527 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_4103527 : Nat := 118140960795 + 4103527 * 2 ^ 59
def prefixEnd_4103527 : Nat := 4983230072969 + 3 ^ 40 * 4103527 * 2
def baseEnd_4103527 : Nat := 2107081729702471665440729

theorem tailTrace_4103527 : CollatzResearch.WordTrace tailWord_4103527 prefixEnd_4103527 2107081729702471665440729 := by
  unfold tailWord_4103527
  simp only [CollatzResearch.WordTrace]
  refine ⟨149667925404629980461052835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99778616936419986974035223 149667925404629980461052835)
  ·
    refine ⟨224501888106944970691579253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149667925404629980461052835 224501888106944970691579253)
    ·
      refine ⟨21047052010026091002335555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224501888106944970691579253 21047052010026091002335555)
      ·
        refine ⟨31570578015039136503503333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21047052010026091002335555 31570578015039136503503333)
        ·
          refine ⟨5919483377819838094406875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31570578015039136503503333 5919483377819838094406875)
          ·
            refine ⟨8879225066729757141610313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919483377819838094406875 8879225066729757141610313)
            ·
              refine ⟨6659418800047317856207735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8879225066729757141610313 6659418800047317856207735)
              ·
                refine ⟨9989128200070976784311603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659418800047317856207735 9989128200070976784311603)
                ·
                  refine ⟨14983692300106465176467405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9989128200070976784311603 14983692300106465176467405)
                  ·
                    refine ⟨5618884612539924441175277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14983692300106465176467405 5618884612539924441175277)
                    ·
                      refine ⟨2107081729702471665440729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5618884612539924441175277 2107081729702471665440729)
                      ·
                        rfl

theorem cell23_4103527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_4103527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103527 prefixEnd_4103527 := by exact prefixLift 4103527
  have htrace : WordTrace (prefixWord ++ tailWord_4103527) baseStart_4103527 baseEnd_4103527 := by
    simpa [prefixWord, tailWord_4103527, baseEnd_4103527] using wordTrace_append hprefix tailTrace_4103527
  have hstable : (prefixWord ++ tailWord_4103527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103527).length < 2 ^ (prefixWord ++ tailWord_4103527).sum := by decide
  have hdescent : baseEnd_4103527 < baseStart_4103527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103561 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 2, 1, 3]
def baseStart_4103561 : Nat := 118140960795 + 4103561 * 2 ^ 59
def prefixEnd_4103561 : Nat := 4983230072969 + 3 ^ 40 * 4103561 * 2
def baseEnd_4103561 : Nat := 2107099188044724532415573

theorem tailTrace_4103561 : CollatzResearch.WordTrace tailWord_4103561 prefixEnd_4103561 2107099188044724532415573 := by
  unfold tailWord_4103561
  simp only [CollatzResearch.WordTrace]
  refine ⟨149669165486506804267790537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99779443657671202845193691 149669165486506804267790537)
  ·
    refine ⟨112251874114880103200842903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149669165486506804267790537 112251874114880103200842903)
    ·
      refine ⟨168377811172320154801264355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112251874114880103200842903 168377811172320154801264355)
      ·
        refine ⟨252566716758480232201896533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168377811172320154801264355 252566716758480232201896533)
        ·
          refine ⟨2959766212013440221115975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 252566716758480232201896533 2959766212013440221115975)
          ·
            refine ⟨4439649318020160331673963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959766212013440221115975 4439649318020160331673963)
            ·
              refine ⟨6659473977030240497510945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439649318020160331673963 6659473977030240497510945)
              ·
                refine ⟨4994605482772680373133209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659473977030240497510945 4994605482772680373133209)
                ·
                  refine ⟨3745954112079510279849907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994605482772680373133209 3745954112079510279849907)
                  ·
                    refine ⟨5618931168119265419774861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3745954112079510279849907 5618931168119265419774861)
                    ·
                      refine ⟨2107099188044724532415573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5618931168119265419774861 2107099188044724532415573)
                      ·
                        rfl

theorem cell23_4103561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 1, 3].length) (baseStart_4103561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103561 prefixEnd_4103561 := by exact prefixLift 4103561
  have htrace : WordTrace (prefixWord ++ tailWord_4103561) baseStart_4103561 baseEnd_4103561 := by
    simpa [prefixWord, tailWord_4103561, baseEnd_4103561] using wordTrace_append hprefix tailTrace_4103561
  have hstable : (prefixWord ++ tailWord_4103561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103561).length < 2 ^ (prefixWord ++ tailWord_4103561).sum := by decide
  have hdescent : baseEnd_4103561 < baseStart_4103561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103563 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 4]
def baseStart_4103563 : Nat := 118140960795 + 4103563 * 2 ^ 59
def prefixEnd_4103563 : Nat := 4983230072969 + 3 ^ 40 * 4103563 * 2
def baseEnd_4103563 : Nat := 2107100215006033524590563

theorem tailTrace_4103563 : CollatzResearch.WordTrace tailWord_4103563 prefixEnd_4103563 2107100215006033524590563 := by
  unfold tailWord_4103563
  simp only [CollatzResearch.WordTrace]
  refine ⟨149669238432499558609363343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99779492288333039072908895 149669238432499558609363343)
  ·
    refine ⟨224503857648749337914045015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149669238432499558609363343 224503857648749337914045015)
    ·
      refine ⟨336755786473124006871067523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224503857648749337914045015 336755786473124006871067523)
      ·
        refine ⟨505133679709686010306601285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336755786473124006871067523 505133679709686010306601285)
        ·
          refine ⟨94712564945566126932487741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505133679709686010306601285 94712564945566126932487741)
          ·
            refine ⟨35517211854587297599682903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94712564945566126932487741 35517211854587297599682903)
            ·
              refine ⟨53275817781880946399524355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35517211854587297599682903 53275817781880946399524355)
              ·
                refine ⟨79913726672821419599286533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53275817781880946399524355 79913726672821419599286533)
                ·
                  refine ⟨14983823751154016174866225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79913726672821419599286533 14983823751154016174866225)
                  ·
                    refine ⟨11237867813365512131149669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14983823751154016174866225 11237867813365512131149669)
                    ·
                      refine ⟨2107100215006033524590563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11237867813365512131149669 2107100215006033524590563)
                      ·
                        rfl

theorem cell23_4103563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 4].length) (baseStart_4103563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103563 prefixEnd_4103563 := by exact prefixLift 4103563
  have htrace : WordTrace (prefixWord ++ tailWord_4103563) baseStart_4103563 baseEnd_4103563 := by
    simpa [prefixWord, tailWord_4103563, baseEnd_4103563] using wordTrace_append hprefix tailTrace_4103563
  have hstable : (prefixWord ++ tailWord_4103563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103563).length < 2 ^ (prefixWord ++ tailWord_4103563).sum := by decide
  have hdescent : baseEnd_4103563 < baseStart_4103563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103573 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 7]
def baseStart_4103573 : Nat := 118140960795 + 4103573 * 2 ^ 59
def prefixEnd_4103573 : Nat := 4983230072969 + 3 ^ 40 * 4103573 * 2
def baseEnd_4103573 : Nat := 234122816645842053940613

theorem tailTrace_4103573 : CollatzResearch.WordTrace tailWord_4103573 prefixEnd_4103573 234122816645842053940613 := by
  unfold tailWord_4103573
  simp only [CollatzResearch.WordTrace]
  refine ⟨149669603162463330317227373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99779735441642220211484915 149669603162463330317227373)
  ·
    refine ⟨56126101185923748868960265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149669603162463330317227373 56126101185923748868960265)
    ·
      refine ⟨42094575889442811651720199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56126101185923748868960265 42094575889442811651720199)
      ·
        refine ⟨63141863834164217477580299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42094575889442811651720199 63141863834164217477580299)
        ·
          refine ⟨94712795751246326216370449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63141863834164217477580299 94712795751246326216370449)
          ·
            refine ⟨71034596813434744662277837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94712795751246326216370449 71034596813434744662277837)
            ·
              refine ⟨26637973805038029248354189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71034596813434744662277837 26637973805038029248354189)
              ·
                refine ⟨9989240176889260968132821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26637973805038029248354189 9989240176889260968132821)
                ·
                  refine ⟨234122816645842053940613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9989240176889260968132821 234122816645842053940613)
                  ·
                    rfl

theorem cell23_4103573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_4103573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103573 prefixEnd_4103573 := by exact prefixLift 4103573
  have htrace : WordTrace (prefixWord ++ tailWord_4103573) baseStart_4103573 baseEnd_4103573 := by
    simpa [prefixWord, tailWord_4103573, baseEnd_4103573] using wordTrace_append hprefix tailTrace_4103573
  have hstable : (prefixWord ++ tailWord_4103573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103573).length < 2 ^ (prefixWord ++ tailWord_4103573).sum := by decide
  have hdescent : baseEnd_4103573 < baseStart_4103573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103603 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 6, 5]
def baseStart_4103603 : Nat := 118140960795 + 4103603 * 2 ^ 59
def prefixEnd_4103603 : Nat := 4983230072969 + 3 ^ 40 * 4103603 * 2
def baseEnd_4103603 : Nat := 702373584744071122696793

theorem tailTrace_4103603 : CollatzResearch.WordTrace tailWord_4103603 prefixEnd_4103603 702373584744071122696793 := by
  unfold tailWord_4103603
  simp only [CollatzResearch.WordTrace]
  refine ⟨149670697352354645440819463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99780464901569763627212975 149670697352354645440819463)
  ·
    refine ⟨224506046028531968161229195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149670697352354645440819463 224506046028531968161229195)
    ·
      refine ⟨336759069042797952241843793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224506046028531968161229195 336759069042797952241843793)
      ·
        refine ⟨252569301782098464181382845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336759069042797952241843793 252569301782098464181382845)
        ·
          refine ⟨94713488168286924068018567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252569301782098464181382845 94713488168286924068018567)
          ·
            refine ⟨142070232252430386102027851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94713488168286924068018567 142070232252430386102027851)
            ·
              refine ⟨213105348378645579153041777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142070232252430386102027851 213105348378645579153041777)
              ·
                refine ⟨159829011283984184364781333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213105348378645579153041777 159829011283984184364781333)
                ·
                  refine ⟨7491984903936758642099125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159829011283984184364781333 7491984903936758642099125)
                  ·
                    refine ⟨702373584744071122696793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7491984903936758642099125 702373584744071122696793)
                    ·
                      rfl

theorem cell23_4103603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 5].length) (baseStart_4103603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103603 prefixEnd_4103603 := by exact prefixLift 4103603
  have htrace : WordTrace (prefixWord ++ tailWord_4103603) baseStart_4103603 baseEnd_4103603 := by
    simpa [prefixWord, tailWord_4103603, baseEnd_4103603] using wordTrace_append hprefix tailTrace_4103603
  have hstable : (prefixWord ++ tailWord_4103603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103603).length < 2 ^ (prefixWord ++ tailWord_4103603).sum := by decide
  have hdescent : baseEnd_4103603 < baseStart_4103603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103610 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2]
def baseStart_4103610 : Nat := 118140960795 + 4103610 * 2 ^ 59
def prefixEnd_4103610 : Nat := 4983230072969 + 3 ^ 40 * 4103610 * 2
def baseEnd_4103610 : Nat := 2107124348596794840702847

theorem tailTrace_4103610 : CollatzResearch.WordTrace tailWord_4103610 prefixEnd_4103610 2107124348596794840702847 := by
  unfold tailWord_4103610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37417738165832321409081071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99780635108886190424216189 37417738165832321409081071)
  ·
    refine ⟨56126607248748482113621607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37417738165832321409081071 56126607248748482113621607)
    ·
      refine ⟨84189910873122723170432411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56126607248748482113621607 84189910873122723170432411)
      ·
        refine ⟨126284866309684084755648617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84189910873122723170432411 126284866309684084755648617)
        ·
          refine ⟨94713649732263063566736463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126284866309684084755648617 94713649732263063566736463)
          ·
            refine ⟨142070474598394595350104695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94713649732263063566736463 142070474598394595350104695)
            ·
              refine ⟨213105711897591893025157043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142070474598394595350104695 213105711897591893025157043)
              ·
                refine ⟨319658567846387839537735565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213105711897591893025157043 319658567846387839537735565)
                ·
                  refine ⟨119871962942395439826650837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319658567846387839537735565 119871962942395439826650837)
                  ·
                    refine ⟨2809499131462393120937129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 119871962942395439826650837 2809499131462393120937129)
                    ·
                      refine ⟨2107124348596794840702847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809499131462393120937129 2107124348596794840702847)
                      ·
                        rfl

theorem cell23_4103610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_4103610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103610 prefixEnd_4103610 := by exact prefixLift 4103610
  have htrace : WordTrace (prefixWord ++ tailWord_4103610) baseStart_4103610 baseEnd_4103610 := by
    simpa [prefixWord, tailWord_4103610, baseEnd_4103610] using wordTrace_append hprefix tailTrace_4103610
  have hstable : (prefixWord ++ tailWord_4103610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103610).length < 2 ^ (prefixWord ++ tailWord_4103610).sum := by decide
  have hdescent : baseEnd_4103610 < baseStart_4103610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103663 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 10]
def baseStart_4103663 : Nat := 118140960795 + 4103663 * 2 ^ 59
def prefixEnd_4103663 : Nat := 4983230072969 + 3 ^ 40 * 4103663 * 2
def baseEnd_4103663 : Nat := 234127951452387014815567

theorem tailTrace_4103663 : CollatzResearch.WordTrace tailWord_4103663 prefixEnd_4103663 234127951452387014815567 := by
  unfold tailWord_4103663
  simp only [CollatzResearch.WordTrace]
  refine ⟨149672885732137275688003643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99781923821424850458669095 149672885732137275688003643)
  ·
    refine ⟨224509328598205913532005465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149672885732137275688003643 224509328598205913532005465)
    ·
      refine ⟨168381996448654435149004099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224509328598205913532005465 168381996448654435149004099)
      ·
        refine ⟨252572994672981652723506149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168381996448654435149004099 252572994672981652723506149)
        ·
          refine ⟨47357436501184059885657403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252572994672981652723506149 47357436501184059885657403)
          ·
            refine ⟨71036154751776089828486105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47357436501184059885657403 71036154751776089828486105)
            ·
              refine ⟨53277116063832067371364579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71036154751776089828486105 53277116063832067371364579)
              ·
                refine ⟨79915674095748101057046869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53277116063832067371364579 79915674095748101057046869)
                ·
                  refine ⟨234127951452387014815567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 79915674095748101057046869 234127951452387014815567)
                  ·
                    rfl

theorem cell23_4103663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 10].length) (baseStart_4103663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103663 prefixEnd_4103663 := by exact prefixLift 4103663
  have htrace : WordTrace (prefixWord ++ tailWord_4103663) baseStart_4103663 baseEnd_4103663 := by
    simpa [prefixWord, tailWord_4103663, baseEnd_4103663] using wordTrace_append hprefix tailTrace_4103663
  have hstable : (prefixWord ++ tailWord_4103663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103663).length < 2 ^ (prefixWord ++ tailWord_4103663).sum := by decide
  have hdescent : baseEnd_4103663 < baseStart_4103663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103677 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_4103677 : Nat := 118140960795 + 4103677 * 2 ^ 59
def prefixEnd_4103677 : Nat := 4983230072969 + 3 ^ 40 * 4103677 * 2
def baseEnd_4103677 : Nat := 2107158751800646078565039

theorem tailTrace_4103677 : CollatzResearch.WordTrace tailWord_4103677 prefixEnd_4103677 2107158751800646078565039 := by
  unfold tailWord_4103677
  simp only [CollatzResearch.WordTrace]
  refine ⟨149673396354086556079013285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99782264236057704052675523 149673396354086556079013285)
  ·
    refine ⟨28063761816391229264814991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149673396354086556079013285 28063761816391229264814991)
    ·
      refine ⟨42095642724586843897222487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28063761816391229264814991 42095642724586843897222487)
      ·
        refine ⟨63143464086880265845833731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42095642724586843897222487 63143464086880265845833731)
        ·
          refine ⟨94715196130320398768750597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63143464086880265845833731 94715196130320398768750597)
          ·
            refine ⟨17759099274435074769140737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94715196130320398768750597 17759099274435074769140737)
            ·
              refine ⟨13319324455826306076855553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17759099274435074769140737 13319324455826306076855553)
              ·
                refine ⟨9989493341869729557641665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13319324455826306076855553 9989493341869729557641665)
                ·
                  refine ⟨7492120006402297168231249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9989493341869729557641665 7492120006402297168231249)
                  ·
                    refine ⟨5619090004801722876173437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7492120006402297168231249 5619090004801722876173437)
                    ·
                      refine ⟨2107158751800646078565039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5619090004801722876173437 2107158751800646078565039)
                      ·
                        rfl

theorem cell23_4103677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_4103677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103677 prefixEnd_4103677 := by exact prefixLift 4103677
  have htrace : WordTrace (prefixWord ++ tailWord_4103677) baseStart_4103677 baseEnd_4103677 := by
    simpa [prefixWord, tailWord_4103677, baseEnd_4103677] using wordTrace_append hprefix tailTrace_4103677
  have hstable : (prefixWord ++ tailWord_4103677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103677).length < 2 ^ (prefixWord ++ tailWord_4103677).sum := by decide
  have hdescent : baseEnd_4103677 < baseStart_4103677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103741 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_4103741 : Nat := 118140960795 + 4103741 * 2 ^ 59
def prefixEnd_4103741 : Nat := 4983230072969 + 3 ^ 40 * 4103741 * 2
def baseEnd_4103741 : Nat := 2107191614562533828164745

theorem tailTrace_4103741 : CollatzResearch.WordTrace tailWord_4103741 prefixEnd_4103741 2107191614562533828164745 := by
  unfold tailWord_4103741
  simp only [CollatzResearch.WordTrace]
  refine ⟨149675730625854695009343077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99783820417236463339562051 149675730625854695009343077)
  ·
    refine ⟨28064199492347755314251827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149675730625854695009343077 28064199492347755314251827)
    ·
      refine ⟨42096299238521632971377741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28064199492347755314251827 42096299238521632971377741)
      ·
        refine ⟨15786112214445612364266653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42096299238521632971377741 15786112214445612364266653)
        ·
          refine ⟨5919792080417104636599995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15786112214445612364266653 5919792080417104636599995)
          ·
            refine ⟨8879688120625656954899993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919792080417104636599995 8879688120625656954899993)
            ·
              refine ⟨6659766090469242716174995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8879688120625656954899993 6659766090469242716174995)
              ·
                refine ⟨9989649135703864074262493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659766090469242716174995 9989649135703864074262493)
                ·
                  refine ⟨3746118425888949027848435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9989649135703864074262493 3746118425888949027848435)
                  ·
                    refine ⟨5619177638833423541772653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3746118425888949027848435 5619177638833423541772653)
                    ·
                      refine ⟨2107191614562533828164745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5619177638833423541772653 2107191614562533828164745)
                      ·
                        rfl

theorem cell23_4103741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_4103741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103741 prefixEnd_4103741 := by exact prefixLift 4103741
  have htrace : WordTrace (prefixWord ++ tailWord_4103741) baseStart_4103741 baseEnd_4103741 := by
    simpa [prefixWord, tailWord_4103741, baseEnd_4103741] using wordTrace_append hprefix tailTrace_4103741
  have hstable : (prefixWord ++ tailWord_4103741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103741).length < 2 ^ (prefixWord ++ tailWord_4103741).sum := by decide
  have hdescent : baseEnd_4103741 < baseStart_4103741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103760 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_4103760 : Nat := 118140960795 + 4103760 * 2 ^ 59
def prefixEnd_4103760 : Nat := 4983230072969 + 3 ^ 40 * 4103760 * 2
def baseEnd_4103760 : Nat := 2107201370694969253827157

theorem tailTrace_4103760 : CollatzResearch.WordTrace tailWord_4103760 prefixEnd_4103760 2107201370694969253827157 := by
  unfold tailWord_4103760
  simp only [CollatzResearch.WordTrace]
  refine ⟨74838211806392930627142367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99784282408523907502856489 74838211806392930627142367)
  ·
    refine ⟨112257317709589395940713551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74838211806392930627142367 112257317709589395940713551)
    ·
      refine ⟨168385976564384093911070327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112257317709589395940713551 168385976564384093911070327)
      ·
        refine ⟨252578964846576140866605491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168385976564384093911070327 252578964846576140866605491)
        ·
          refine ⟨378868447269864211299908237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252578964846576140866605491 378868447269864211299908237)
          ·
            refine ⟨142075667726199079237465589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378868447269864211299908237 142075667726199079237465589)
            ·
              refine ⟨13319593849331163678512399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142075667726199079237465589 13319593849331163678512399)
              ·
                refine ⟨19979390773996745517768599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13319593849331163678512399 19979390773996745517768599)
                ·
                  refine ⟨29969086160995118276652899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19979390773996745517768599 29969086160995118276652899)
                  ·
                    refine ⟨44953629241492677414979349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29969086160995118276652899 44953629241492677414979349)
                    ·
                      refine ⟨2107201370694969253827157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44953629241492677414979349 2107201370694969253827157)
                      ·
                        rfl

theorem cell23_4103760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_4103760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103760 prefixEnd_4103760 := by exact prefixLift 4103760
  have htrace : WordTrace (prefixWord ++ tailWord_4103760) baseStart_4103760 baseEnd_4103760 := by
    simpa [prefixWord, tailWord_4103760, baseEnd_4103760] using wordTrace_append hprefix tailTrace_4103760
  have hstable : (prefixWord ++ tailWord_4103760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103760).length < 2 ^ (prefixWord ++ tailWord_4103760).sum := by decide
  have hdescent : baseEnd_4103760 < baseStart_4103760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103764 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_4103764 : Nat := 118140960795 + 4103764 * 2 ^ 59
def prefixEnd_4103764 : Nat := 4983230072969 + 3 ^ 40 * 4103764 * 2
def baseEnd_4103764 : Nat := 2107203424617587238177139

theorem tailTrace_4103764 : CollatzResearch.WordTrace tailWord_4103764 prefixEnd_4103764 2107203424617587238177139 := by
  unfold tailWord_4103764
  simp only [CollatzResearch.WordTrace]
  refine ⟨74838284752385684968715173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99784379669847579958286897 74838284752385684968715173)
  ·
    refine ⟨14032178391072315931634095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74838284752385684968715173 14032178391072315931634095)
    ·
      refine ⟨21048267586608473897451143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14032178391072315931634095 21048267586608473897451143)
      ·
        refine ⟨31572401379912710846176715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21048267586608473897451143 31572401379912710846176715)
        ·
          refine ⟨47358602069869066269265073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31572401379912710846176715 47358602069869066269265073)
          ·
            refine ⟨35518951552401799701948805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47358602069869066269265073 35518951552401799701948805)
            ·
              refine ⟨6659803416075337444115401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35518951552401799701948805 6659803416075337444115401)
              ·
                refine ⟨4994852562056503083086551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6659803416075337444115401 4994852562056503083086551)
                ·
                  refine ⟨7492278843084754624629827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994852562056503083086551 7492278843084754624629827)
                  ·
                    refine ⟨11238418264627131936944741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7492278843084754624629827 11238418264627131936944741)
                    ·
                      refine ⟨2107203424617587238177139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11238418264627131936944741 2107203424617587238177139)
                      ·
                        rfl

theorem cell23_4103764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_4103764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103764 prefixEnd_4103764 := by exact prefixLift 4103764
  have htrace : WordTrace (prefixWord ++ tailWord_4103764) baseStart_4103764 baseEnd_4103764 := by
    simpa [prefixWord, tailWord_4103764, baseEnd_4103764] using wordTrace_append hprefix tailTrace_4103764
  have hstable : (prefixWord ++ tailWord_4103764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103764).length < 2 ^ (prefixWord ++ tailWord_4103764).sum := by decide
  have hdescent : baseEnd_4103764 < baseStart_4103764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103784 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4103784 : Nat := 118140960795 + 4103784 * 2 ^ 59
def prefixEnd_4103784 : Nat := 4983230072969 + 3 ^ 40 * 4103784 * 2
def baseEnd_4103784 : Nat := 2107213694230677159927047

theorem tailTrace_4103784 : CollatzResearch.WordTrace tailWord_4103784 prefixEnd_4103784 2107213694230677159927047 := by
  unfold tailWord_4103784
  simp only [CollatzResearch.WordTrace]
  refine ⟨74838649482349456676579203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99784865976465942235438937 74838649482349456676579203)
  ·
    refine ⟨112257974223524185014868805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74838649482349456676579203 112257974223524185014868805)
    ·
      refine ⟨21048370166910784690287901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112257974223524185014868805 21048370166910784690287901)
      ·
        refine ⟨7893138812591544258857963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21048370166910784690287901 7893138812591544258857963)
        ·
          refine ⟨11839708218887316388286945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7893138812591544258857963 11839708218887316388286945)
          ·
            refine ⟨8879781164165487291215209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11839708218887316388286945 8879781164165487291215209)
            ·
              refine ⟨6659835873124115468411407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8879781164165487291215209 6659835873124115468411407)
              ·
                refine ⟨9989753809686173202617111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659835873124115468411407 9989753809686173202617111)
                ·
                  refine ⟨14984630714529259803925667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9989753809686173202617111 14984630714529259803925667)
                  ·
                    refine ⟨22476946071793889705888501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14984630714529259803925667 22476946071793889705888501)
                    ·
                      refine ⟨2107213694230677159927047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22476946071793889705888501 2107213694230677159927047)
                      ·
                        rfl

theorem cell23_4103784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4103784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103784 prefixEnd_4103784 := by exact prefixLift 4103784
  have htrace : WordTrace (prefixWord ++ tailWord_4103784) baseStart_4103784 baseEnd_4103784 := by
    simpa [prefixWord, tailWord_4103784, baseEnd_4103784] using wordTrace_append hprefix tailTrace_4103784
  have hstable : (prefixWord ++ tailWord_4103784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103784).length < 2 ^ (prefixWord ++ tailWord_4103784).sum := by decide
  have hdescent : baseEnd_4103784 < baseStart_4103784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103798 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_4103798 : Nat := 118140960795 + 4103798 * 2 ^ 59
def prefixEnd_4103798 : Nat := 4983230072969 + 3 ^ 40 * 4103798 * 2
def baseEnd_4103798 : Nat := 2107220882959840105151983

theorem tailTrace_4103798 : CollatzResearch.WordTrace tailWord_4103798 prefixEnd_4103798 2107220882959840105151983 := by
  unfold tailWord_4103798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354863099165512109010503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99785206391098795829445365 9354863099165512109010503)
  ·
    refine ⟨14032294648748268163515755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9354863099165512109010503 14032294648748268163515755)
    ·
      refine ⟨21048441973122402245273633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14032294648748268163515755 21048441973122402245273633)
      ·
        refine ⟨15786331479841801683955225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21048441973122402245273633 15786331479841801683955225)
        ·
          refine ⟨11839748609881351262966419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15786331479841801683955225 11839748609881351262966419)
          ·
            refine ⟨17759622914822026894449629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11839748609881351262966419 17759622914822026894449629)
            ·
              refine ⟨6659858593058260085418611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17759622914822026894449629 6659858593058260085418611)
              ·
                refine ⟨9989787889587390128127917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659858593058260085418611 9989787889587390128127917)
                ·
                  refine ⟨3746170458595271298047969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9989787889587390128127917 3746170458595271298047969)
                  ·
                    refine ⟨2809627843946453473535977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3746170458595271298047969 2809627843946453473535977)
                    ·
                      refine ⟨2107220882959840105151983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809627843946453473535977 2107220882959840105151983)
                      ·
                        rfl

theorem cell23_4103798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_4103798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103798 prefixEnd_4103798 := by exact prefixLift 4103798
  have htrace : WordTrace (prefixWord ++ tailWord_4103798) baseStart_4103798 baseEnd_4103798 := by
    simpa [prefixWord, tailWord_4103798, baseEnd_4103798] using wordTrace_append hprefix tailTrace_4103798
  have hstable : (prefixWord ++ tailWord_4103798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103798).length < 2 ^ (prefixWord ++ tailWord_4103798).sum := by decide
  have hdescent : baseEnd_4103798 < baseStart_4103798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103871 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 2, 2, 2]
def baseStart_4103871 : Nat := 118140960795 + 4103871 * 2 ^ 59
def prefixEnd_4103871 : Nat := 4983230072969 + 3 ^ 40 * 4103871 * 2
def baseEnd_4103871 : Nat := 2107258367047618319539147

theorem tailTrace_4103871 : CollatzResearch.WordTrace tailWord_4103871 prefixEnd_4103871 2107258367047618319539147 := by
  unfold tailWord_4103871
  simp only [CollatzResearch.WordTrace]
  refine ⟨149680472115383727211575467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99786981410255818141050311 149680472115383727211575467)
  ·
    refine ⟨224520708173075590817363201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149680472115383727211575467 224520708173075590817363201)
    ·
      refine ⟨168390531129806693113022401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224520708173075590817363201 168390531129806693113022401)
      ·
        refine ⟨126292898347355019834766801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168390531129806693113022401 126292898347355019834766801)
        ·
          refine ⟨94719673760516264876075101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126292898347355019834766801 94719673760516264876075101)
          ·
            refine ⟨35519877660193599328528163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94719673760516264876075101 35519877660193599328528163)
            ·
              refine ⟨53279816490290398992792245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35519877660193599328528163 53279816490290398992792245)
              ·
                refine ⟨4994982795964724905574273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53279816490290398992792245 4994982795964724905574273)
                ·
                  refine ⟨3746237096973543679180705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994982795964724905574273 3746237096973543679180705)
                  ·
                    refine ⟨2809677822730157759385529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3746237096973543679180705 2809677822730157759385529)
                    ·
                      refine ⟨2107258367047618319539147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809677822730157759385529 2107258367047618319539147)
                      ·
                        rfl

theorem cell23_4103871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_4103871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103871 prefixEnd_4103871 := by exact prefixLift 4103871
  have htrace : WordTrace (prefixWord ++ tailWord_4103871) baseStart_4103871 baseEnd_4103871 := by
    simpa [prefixWord, tailWord_4103871, baseEnd_4103871] using wordTrace_append hprefix tailTrace_4103871
  have hstable : (prefixWord ++ tailWord_4103871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103871).length < 2 ^ (prefixWord ++ tailWord_4103871).sum := by decide
  have hdescent : baseEnd_4103871 < baseStart_4103871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103905 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_4103905 : Nat := 118140960795 + 4103905 * 2 ^ 59
def prefixEnd_4103905 : Nat := 4983230072969 + 3 ^ 40 * 4103905 * 2
def baseEnd_4103905 : Nat := 2107275825389871186513991

theorem tailTrace_4103905 : CollatzResearch.WordTrace tailWord_4103905 prefixEnd_4103905 2107275825389871186513991 := by
  unfold tailWord_4103905
  simp only [CollatzResearch.WordTrace]
  refine ⟨149681712197260551018313169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99787808131507034012208779 149681712197260551018313169)
  ·
    refine ⟨112261284147945413263734877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149681712197260551018313169 112261284147945413263734877)
    ·
      refine ⟨42097981555479529973900579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112261284147945413263734877 42097981555479529973900579)
      ·
        refine ⟨63146972333219294960850869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42097981555479529973900579 63146972333219294960850869)
        ·
          refine ⟨5920028656239308902579769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63146972333219294960850869 5920028656239308902579769)
          ·
            refine ⟨4440021492179481676934827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5920028656239308902579769 4440021492179481676934827)
            ·
              refine ⟨6660032238269222515402241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4440021492179481676934827 6660032238269222515402241)
              ·
                refine ⟨4995024178701916886551681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6660032238269222515402241 4995024178701916886551681)
                ·
                  refine ⟨3746268134026437664913761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4995024178701916886551681 3746268134026437664913761)
                  ·
                    refine ⟨2809701100519828248685321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3746268134026437664913761 2809701100519828248685321)
                    ·
                      refine ⟨2107275825389871186513991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809701100519828248685321 2107275825389871186513991)
                      ·
                        rfl

theorem cell23_4103905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_4103905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103905 prefixEnd_4103905 := by exact prefixLift 4103905
  have htrace : WordTrace (prefixWord ++ tailWord_4103905) baseStart_4103905 baseEnd_4103905 := by
    simpa [prefixWord, tailWord_4103905, baseEnd_4103905] using wordTrace_append hprefix tailTrace_4103905
  have hstable : (prefixWord ++ tailWord_4103905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103905).length < 2 ^ (prefixWord ++ tailWord_4103905).sum := by decide
  have hdescent : baseEnd_4103905 < baseStart_4103905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103911 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 7]
def baseStart_4103911 : Nat := 118140960795 + 4103911 * 2 ^ 59
def prefixEnd_4103911 : Nat := 4983230072969 + 3 ^ 40 * 4103911 * 2
def baseEnd_4103911 : Nat := 234142100697088684782107

theorem tailTrace_4103911 : CollatzResearch.WordTrace tailWord_4103911 prefixEnd_4103911 234142100697088684782107 := by
  unfold tailWord_4103911
  simp only [CollatzResearch.WordTrace]
  refine ⟨149681931035238814043031587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99787954023492542695354391 149681931035238814043031587)
  ·
    refine ⟨224522896552858221064547381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149681931035238814043031587 224522896552858221064547381)
    ·
      refine ⟨21049021551830458224801317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224522896552858221064547381 21049021551830458224801317)
      ·
        refine ⟨3946691540968210917150247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21049021551830458224801317 3946691540968210917150247)
        ·
          refine ⟨5920037311452316375725371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3946691540968210917150247 5920037311452316375725371)
          ·
            refine ⟨8880055967178474563588057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920037311452316375725371 8880055967178474563588057)
            ·
              refine ⟨6660041975383855922691043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8880055967178474563588057 6660041975383855922691043)
              ·
                refine ⟨9990062963075783884036565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6660041975383855922691043 9990062963075783884036565)
                ·
                  refine ⟨234142100697088684782107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9990062963075783884036565 234142100697088684782107)
                  ·
                    rfl

theorem cell23_4103911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 7].length) (baseStart_4103911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103911 prefixEnd_4103911 := by exact prefixLift 4103911
  have htrace : WordTrace (prefixWord ++ tailWord_4103911) baseStart_4103911 baseEnd_4103911 := by
    simpa [prefixWord, tailWord_4103911, baseEnd_4103911] using wordTrace_append hprefix tailTrace_4103911
  have hstable : (prefixWord ++ tailWord_4103911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103911).length < 2 ^ (prefixWord ++ tailWord_4103911).sum := by decide
  have hdescent : baseEnd_4103911 < baseStart_4103911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103914 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_4103914 : Nat := 118140960795 + 4103914 * 2 ^ 59
def prefixEnd_4103914 : Nat := 4983230072969 + 3 ^ 40 * 4103914 * 2
def baseEnd_4103914 : Nat := 2107280446715761651301449

theorem tailTrace_4103914 : CollatzResearch.WordTrace tailWord_4103914 prefixEnd_4103914 2107280446715761651301449 := by
  unfold tailWord_4103914
  simp only [CollatzResearch.WordTrace]
  refine ⟨37420510113556986388847699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99788026969485297036927197 37420510113556986388847699)
  ·
    refine ⟨56130765170335479583271549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37420510113556986388847699 56130765170335479583271549)
    ·
      refine ⟨21049036938875804843726831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56130765170335479583271549 21049036938875804843726831)
      ·
        refine ⟨31573555408313707265590247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21049036938875804843726831 31573555408313707265590247)
        ·
          refine ⟨47360333112470560898385371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31573555408313707265590247 47360333112470560898385371)
          ·
            refine ⟨71040499668705841347578057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47360333112470560898385371 71040499668705841347578057)
            ·
              refine ⟨53280374751529381010683543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71040499668705841347578057 53280374751529381010683543)
              ·
                refine ⟨79920562127294071516025315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53280374751529381010683543 79920562127294071516025315)
                ·
                  refine ⟨119880843190941107274037973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79920562127294071516025315 119880843190941107274037973)
                  ·
                    refine ⟨2809707262287682201735265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 119880843190941107274037973 2809707262287682201735265)
                    ·
                      refine ⟨2107280446715761651301449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809707262287682201735265 2107280446715761651301449)
                      ·
                        rfl

theorem cell23_4103914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_4103914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103914 prefixEnd_4103914 := by exact prefixLift 4103914
  have htrace : WordTrace (prefixWord ++ tailWord_4103914) baseStart_4103914 baseEnd_4103914 := by
    simpa [prefixWord, tailWord_4103914, baseEnd_4103914] using wordTrace_append hprefix tailTrace_4103914
  have hstable : (prefixWord ++ tailWord_4103914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103914).length < 2 ^ (prefixWord ++ tailWord_4103914).sum := by decide
  have hdescent : baseEnd_4103914 < baseStart_4103914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103927 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_4103927 : Nat := 118140960795 + 4103927 * 2 ^ 59
def prefixEnd_4103927 : Nat := 4983230072969 + 3 ^ 40 * 4103927 * 2
def baseEnd_4103927 : Nat := 2107287121964270100438889

theorem tailTrace_4103927 : CollatzResearch.WordTrace tailWord_4103927 prefixEnd_4103927 2107287121964270100438889 := by
  unfold tailWord_4103927
  simp only [CollatzResearch.WordTrace]
  refine ⟨149682514603180848775614035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99788343068787232517076023 149682514603180848775614035)
  ·
    refine ⟨224523771904771273163421053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149682514603180848775614035 224523771904771273163421053)
    ·
      refine ⟨84196414464289227436282895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224523771904771273163421053 84196414464289227436282895)
      ·
        refine ⟨126294621696433841154424343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84196414464289227436282895 126294621696433841154424343)
        ·
          refine ⟨189441932544650761731636515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126294621696433841154424343 189441932544650761731636515)
          ·
            refine ⟨284162898816976142597454773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189441932544650761731636515 284162898816976142597454773)
            ·
              refine ⟨26640271764091513368511385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284162898816976142597454773 26640271764091513368511385)
              ·
                refine ⟨19980203823068635026383539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26640271764091513368511385 19980203823068635026383539)
                ·
                  refine ⟨29970305734602952539575309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19980203823068635026383539 29970305734602952539575309)
                  ·
                    refine ⟨11238864650476107202340741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29970305734602952539575309 11238864650476107202340741)
                    ·
                      refine ⟨2107287121964270100438889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11238864650476107202340741 2107287121964270100438889)
                      ·
                        rfl

theorem cell23_4103927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_4103927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103927 prefixEnd_4103927 := by exact prefixLift 4103927
  have htrace : WordTrace (prefixWord ++ tailWord_4103927) baseStart_4103927 baseEnd_4103927 := by
    simpa [prefixWord, tailWord_4103927, baseEnd_4103927] using wordTrace_append hprefix tailTrace_4103927
  have hstable : (prefixWord ++ tailWord_4103927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103927).length < 2 ^ (prefixWord ++ tailWord_4103927).sum := by decide
  have hdescent : baseEnd_4103927 < baseStart_4103927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103942 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4103942 : Nat := 118140960795 + 4103942 * 2 ^ 59
def prefixEnd_4103942 : Nat := 4983230072969 + 3 ^ 40 * 4103942 * 2
def baseEnd_4103942 : Nat := 2107294824174087541751321

theorem tailTrace_4103942 : CollatzResearch.WordTrace tailWord_4103942 prefixEnd_4103942 2107294824174087541751321 := by
  unfold tailWord_4103942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4677595678066453323044065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99788707798751004224940053 4677595678066453323044065)
  ·
    refine ⟨3508196758549839992283049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4677595678066453323044065 3508196758549839992283049)
    ·
      refine ⟨2631147568912379994212287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3508196758549839992283049 2631147568912379994212287)
      ·
        refine ⟨3946721353368569991318431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631147568912379994212287 3946721353368569991318431)
        ·
          refine ⟨5920082030052854986977647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3946721353368569991318431 5920082030052854986977647)
          ·
            refine ⟨8880123045079282480466471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920082030052854986977647 8880123045079282480466471)
            ·
              refine ⟨13320184567618923720699707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8880123045079282480466471 13320184567618923720699707)
              ·
                refine ⟨19980276851428385581049561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13320184567618923720699707 19980276851428385581049561)
                ·
                  refine ⟨14985207638571289185787171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19980276851428385581049561 14985207638571289185787171)
                  ·
                    refine ⟨22477811457856933778680757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14985207638571289185787171 22477811457856933778680757)
                    ·
                      refine ⟨2107294824174087541751321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22477811457856933778680757 2107294824174087541751321)
                      ·
                        rfl

theorem cell23_4103942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4103942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103942 prefixEnd_4103942 := by exact prefixLift 4103942
  have htrace : WordTrace (prefixWord ++ tailWord_4103942) baseStart_4103942 baseEnd_4103942 := by
    simpa [prefixWord, tailWord_4103942, baseEnd_4103942] using wordTrace_append hprefix tailTrace_4103942
  have hstable : (prefixWord ++ tailWord_4103942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103942).length < 2 ^ (prefixWord ++ tailWord_4103942).sum := by decide
  have hdescent : baseEnd_4103942 < baseStart_4103942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103944 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_4103944 : Nat := 118140960795 + 4103944 * 2 ^ 59
def prefixEnd_4103944 : Nat := 4983230072969 + 3 ^ 40 * 4103944 * 2
def baseEnd_4103944 : Nat := 2107295851135396533926311

theorem tailTrace_4103944 : CollatzResearch.WordTrace tailWord_4103944 prefixEnd_4103944 2107295851135396533926311 := by
  unfold tailWord_4103944
  simp only [CollatzResearch.WordTrace]
  refine ⟨74841567322059630339491443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99788756429412840452655257 74841567322059630339491443)
  ·
    refine ⟨112262350983089445509237165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74841567322059630339491443 112262350983089445509237165)
    ·
      refine ⟨42098381618658542065963937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112262350983089445509237165 42098381618658542065963937)
      ·
        refine ⟨31573786213993906549472953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42098381618658542065963937 31573786213993906549472953)
        ·
          refine ⟨23680339660495429912104715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31573786213993906549472953 23680339660495429912104715)
          ·
            refine ⟨35520509490743144868157073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23680339660495429912104715 35520509490743144868157073)
            ·
              refine ⟨26640382118057358651117805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35520509490743144868157073 26640382118057358651117805)
              ·
                refine ⟨9990143294271509494169177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26640382118057358651117805 9990143294271509494169177)
                ·
                  refine ⟨7492607470703632120626883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9990143294271509494169177 7492607470703632120626883)
                  ·
                    refine ⟨11238911206055448180940325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7492607470703632120626883 11238911206055448180940325)
                    ·
                      refine ⟨2107295851135396533926311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11238911206055448180940325 2107295851135396533926311)
                      ·
                        rfl

theorem cell23_4103944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_4103944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103944 prefixEnd_4103944 := by exact prefixLift 4103944
  have htrace : WordTrace (prefixWord ++ tailWord_4103944) baseStart_4103944 baseEnd_4103944 := by
    simpa [prefixWord, tailWord_4103944, baseEnd_4103944] using wordTrace_append hprefix tailTrace_4103944
  have hstable : (prefixWord ++ tailWord_4103944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103944).length < 2 ^ (prefixWord ++ tailWord_4103944).sum := by decide
  have hdescent : baseEnd_4103944 < baseStart_4103944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103967 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 8]
def baseStart_4103967 : Nat := 118140960795 + 4103967 * 2 ^ 59
def prefixEnd_4103967 : Nat := 4983230072969 + 3 ^ 40 * 4103967 * 2
def baseEnd_4103967 : Nat := 234145295687827771548745

theorem tailTrace_4103967 : CollatzResearch.WordTrace tailWord_4103967 prefixEnd_4103967 234145295687827771548745 := by
  unfold tailWord_4103967
  simp only [CollatzResearch.WordTrace]
  refine ⟨149683973523035935607070155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99789315682023957071380103 149683973523035935607070155)
  ·
    refine ⟨224525960284553903410605233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149683973523035935607070155 224525960284553903410605233)
    ·
      refine ⟨168394470213415427557953925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224525960284553903410605233 168394470213415427557953925)
      ·
        refine ⟨31573963165015392667116361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168394470213415427557953925 31573963165015392667116361)
        ·
          refine ⟨23680472373761544500337271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31573963165015392667116361 23680472373761544500337271)
          ·
            refine ⟨35520708560642316750505907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23680472373761544500337271 35520708560642316750505907)
            ·
              refine ⟨53281062840963475125758861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35520708560642316750505907 53281062840963475125758861)
              ·
                refine ⟨19980398565361303172159573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53281062840963475125758861 19980398565361303172159573)
                ·
                  refine ⟨234145295687827771548745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19980398565361303172159573 234145295687827771548745)
                  ·
                    rfl

theorem cell23_4103967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 8].length) (baseStart_4103967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103967 prefixEnd_4103967 := by exact prefixLift 4103967
  have htrace : WordTrace (prefixWord ++ tailWord_4103967) baseStart_4103967 baseEnd_4103967 := by
    simpa [prefixWord, tailWord_4103967, baseEnd_4103967] using wordTrace_append hprefix tailTrace_4103967
  have hstable : (prefixWord ++ tailWord_4103967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103967).length < 2 ^ (prefixWord ++ tailWord_4103967).sum := by decide
  have hdescent : baseEnd_4103967 < baseStart_4103967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103971 : List Nat := [1, 1, 1, 4, 2, 1, 2, 6, 1, 4]
def baseStart_4103971 : Nat := 118140960795 + 4103971 * 2 ^ 59
def prefixEnd_4103971 : Nat := 4983230072969 + 3 ^ 40 * 4103971 * 2
def baseEnd_4103971 : Nat := 702436571704355976096229

theorem tailTrace_4103971 : CollatzResearch.WordTrace tailWord_4103971 prefixEnd_4103971 702436571704355976096229 := by
  unfold tailWord_4103971
  simp only [CollatzResearch.WordTrace]
  refine ⟨149684119415021444290215767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99789412943347629526810511 149684119415021444290215767)
  ·
    refine ⟨224526179122532166435323651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149684119415021444290215767 224526179122532166435323651)
    ·
      refine ⟨336789268683798249652985477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224526179122532166435323651 336789268683798249652985477)
      ·
        refine ⟨63147987878212171809934777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336789268683798249652985477 63147987878212171809934777)
        ·
          refine ⟨47360990908659128857451083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63147987878212171809934777 47360990908659128857451083)
          ·
            refine ⟨71041486362988693286176625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47360990908659128857451083 71041486362988693286176625)
            ·
              refine ⟨53281114772241519964632469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71041486362988693286176625 53281114772241519964632469)
              ·
                refine ⟨2497552254948821248342147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53281114772241519964632469 2497552254948821248342147)
                ·
                  refine ⟨3746328382423231872513221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497552254948821248342147 3746328382423231872513221)
                  ·
                    refine ⟨702436571704355976096229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3746328382423231872513221 702436571704355976096229)
                    ·
                      rfl

theorem cell23_4103971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 4].length) (baseStart_4103971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103971 prefixEnd_4103971 := by exact prefixLift 4103971
  have htrace : WordTrace (prefixWord ++ tailWord_4103971) baseStart_4103971 baseEnd_4103971 := by
    simpa [prefixWord, tailWord_4103971, baseEnd_4103971] using wordTrace_append hprefix tailTrace_4103971
  have hstable : (prefixWord ++ tailWord_4103971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103971).length < 2 ^ (prefixWord ++ tailWord_4103971).sum := by decide
  have hdescent : baseEnd_4103971 < baseStart_4103971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103998 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_4103998 : Nat := 118140960795 + 4103998 * 2 ^ 59
def prefixEnd_4103998 : Nat := 4983230072969 + 3 ^ 40 * 4103998 * 2
def baseEnd_4103998 : Nat := 2107323579090739322651063

theorem tailTrace_4103998 : CollatzResearch.WordTrace tailWord_4103998 prefixEnd_4103998 2107323579090739322651063 := by
  unfold tailWord_4103998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710638023240453487681081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99790069457282418600965765 18710638023240453487681081)
  ·
    refine ⟨14032978517430340115760811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18710638023240453487681081 14032978517430340115760811)
    ·
      refine ⟨21049467776145510173641217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14032978517430340115760811 21049467776145510173641217)
      ·
        refine ⟨15787100832109132630230913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21049467776145510173641217 15787100832109132630230913)
        ·
          refine ⟨11840325624081849472673185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15787100832109132630230913 11840325624081849472673185)
          ·
            refine ⟨8880244218061387104504889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11840325624081849472673185 8880244218061387104504889)
            ·
              refine ⟨6660183163546040328378667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8880244218061387104504889 6660183163546040328378667)
              ·
                refine ⟨9990274745319060492568001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6660183163546040328378667 9990274745319060492568001)
                ·
                  refine ⟨7492706058989295369426001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9990274745319060492568001 7492706058989295369426001)
                  ·
                    refine ⟨5619529544241971527069501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7492706058989295369426001 5619529544241971527069501)
                    ·
                      refine ⟨2107323579090739322651063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5619529544241971527069501 2107323579090739322651063)
                      ·
                        rfl

theorem cell23_4103998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_4103998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4103998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4103998 prefixEnd_4103998 := by exact prefixLift 4103998
  have htrace : WordTrace (prefixWord ++ tailWord_4103998) baseStart_4103998 baseEnd_4103998 := by
    simpa [prefixWord, tailWord_4103998, baseEnd_4103998] using wordTrace_append hprefix tailTrace_4103998
  have hstable : (prefixWord ++ tailWord_4103998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103998).length < 2 ^ (prefixWord ++ tailWord_4103998).sum := by decide
  have hdescent : baseEnd_4103998 < baseStart_4103998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104044 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_4104044 : Nat := 118140960795 + 4104044 * 2 ^ 59
def prefixEnd_4104044 : Nat := 4983230072969 + 3 ^ 40 * 4104044 * 2
def baseEnd_4104044 : Nat := 702449066400282047558617

theorem tailTrace_4104044 : CollatzResearch.WordTrace tailWord_4104044 prefixEnd_4104044 702449066400282047558617 := by
  unfold tailWord_4104044
  simp only [CollatzResearch.WordTrace]
  refine ⟨74843390971878488878811593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99791187962504651838415457 74843390971878488878811593)
  ·
    refine ⟨56132543228908866659108695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74843390971878488878811593 56132543228908866659108695)
    ·
      refine ⟨84198814843363299988663043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56132543228908866659108695 84198814843363299988663043)
      ·
        refine ⟨126298222265044949982994565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84198814843363299988663043 126298222265044949982994565)
        ·
          refine ⟨23680916674695928121811481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126298222265044949982994565 23680916674695928121811481)
          ·
            refine ⟨17760687506021946091358611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23680916674695928121811481 17760687506021946091358611)
            ·
              refine ⟨26641031259032919137037917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17760687506021946091358611 26641031259032919137037917)
              ·
                refine ⟨9990386722137344676389219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26641031259032919137037917 9990386722137344676389219)
                ·
                  refine ⟨14985580083206017014583829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9990386722137344676389219 14985580083206017014583829)
                  ·
                    refine ⟨702449066400282047558617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14985580083206017014583829 702449066400282047558617)
                    ·
                      rfl

theorem cell23_4104044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_4104044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104044 prefixEnd_4104044 := by exact prefixLift 4104044
  have htrace : WordTrace (prefixWord ++ tailWord_4104044) baseStart_4104044 baseEnd_4104044 := by
    simpa [prefixWord, tailWord_4104044, baseEnd_4104044] using wordTrace_append hprefix tailTrace_4104044
  have hstable : (prefixWord ++ tailWord_4104044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104044).length < 2 ^ (prefixWord ++ tailWord_4104044).sum := by decide
  have hdescent : baseEnd_4104044 < baseStart_4104044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104062 : List Nat := [4, 2, 3, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4104062 : Nat := 118140960795 + 4104062 * 2 ^ 59
def prefixEnd_4104062 : Nat := 4983230072969 + 3 ^ 40 * 4104062 * 2
def baseEnd_4104062 : Nat := 2107356441852627072250769

theorem tailTrace_4104062 : CollatzResearch.WordTrace tailWord_4104062 prefixEnd_4104062 2107356441852627072250769 := by
  unfold tailWord_4104062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710929807211470853972305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99791625638461177887852293 18710929807211470853972305)
  ·
    refine ⟨14033197355408603140479229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18710929807211470853972305 14033197355408603140479229)
    ·
      refine ⟨5262449008278226177679711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14033197355408603140479229 5262449008278226177679711)
      ·
        refine ⟨7893673512417339266519567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5262449008278226177679711 7893673512417339266519567)
        ·
          refine ⟨11840510268626008899779351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7893673512417339266519567 11840510268626008899779351)
          ·
            refine ⟨17760765402939013349669027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11840510268626008899779351 17760765402939013349669027)
            ·
              refine ⟨26641148104408520024503541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17760765402939013349669027 26641148104408520024503541)
              ·
                refine ⟨2497607634788298752297207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26641148104408520024503541 2497607634788298752297207)
                ·
                  refine ⟨3746411452182448128445811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497607634788298752297207 3746411452182448128445811)
                  ·
                    refine ⟨5619617178273672192668717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3746411452182448128445811 5619617178273672192668717)
                    ·
                      refine ⟨2107356441852627072250769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5619617178273672192668717 2107356441852627072250769)
                      ·
                        rfl

theorem cell23_4104062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4104062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104062 prefixEnd_4104062 := by exact prefixLift 4104062
  have htrace : WordTrace (prefixWord ++ tailWord_4104062) baseStart_4104062 baseEnd_4104062 := by
    simpa [prefixWord, tailWord_4104062, baseEnd_4104062] using wordTrace_append hprefix tailTrace_4104062
  have hstable : (prefixWord ++ tailWord_4104062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104062).length < 2 ^ (prefixWord ++ tailWord_4104062).sum := by decide
  have hdescent : baseEnd_4104062 < baseStart_4104062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104064 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_4104064 : Nat := 118140960795 + 4104064 * 2 ^ 59
def prefixEnd_4104064 : Nat := 4983230072969 + 3 ^ 40 * 4104064 * 2
def baseEnd_4104064 : Nat := 2107357468813936064425759

theorem tailTrace_4104064 : CollatzResearch.WordTrace tailWord_4104064 prefixEnd_4104064 2107357468813936064425759 := by
  unfold tailWord_4104064
  simp only [CollatzResearch.WordTrace]
  refine ⟨74843755701842260586675623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99791674269123014115567497 74843755701842260586675623)
  ·
    refine ⟨112265633552763390880013435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74843755701842260586675623 112265633552763390880013435)
    ·
      refine ⟨168398450329145086320020153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112265633552763390880013435 168398450329145086320020153)
      ·
        refine ⟨126298837746858814740015115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168398450329145086320020153 126298837746858814740015115)
        ·
          refine ⟨189448256620288222110022673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126298837746858814740015115 189448256620288222110022673)
          ·
            refine ⟨142086192465216166582517005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189448256620288222110022673 142086192465216166582517005)
            ·
              refine ⟨53282322174456062468443877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142086192465216166582517005 53282322174456062468443877)
              ·
                refine ⟨9990435407710511712833227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53282322174456062468443877 9990435407710511712833227)
                ·
                  refine ⟨14985653111565767569249841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9990435407710511712833227 14985653111565767569249841)
                  ·
                    refine ⟨11239239833674325676937381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14985653111565767569249841 11239239833674325676937381)
                    ·
                      refine ⟨2107357468813936064425759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11239239833674325676937381 2107357468813936064425759)
                      ·
                        rfl

theorem cell23_4104064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_4104064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104064 prefixEnd_4104064 := by exact prefixLift 4104064
  have htrace : WordTrace (prefixWord ++ tailWord_4104064) baseStart_4104064 baseEnd_4104064 := by
    simpa [prefixWord, tailWord_4104064, baseEnd_4104064] using wordTrace_append hprefix tailTrace_4104064
  have hstable : (prefixWord ++ tailWord_4104064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104064).length < 2 ^ (prefixWord ++ tailWord_4104064).sum := by decide
  have hdescent : baseEnd_4104064 < baseStart_4104064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104068 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_4104068 : Nat := 118140960795 + 4104068 * 2 ^ 59
def prefixEnd_4104068 : Nat := 4983230072969 + 3 ^ 40 * 4104068 * 2
def baseEnd_4104068 : Nat := 2107359522736554048775741

theorem tailTrace_4104068 : CollatzResearch.WordTrace tailWord_4104068 prefixEnd_4104068 2107359522736554048775741 := by
  unfold tailWord_4104068
  simp only [CollatzResearch.WordTrace]
  refine ⟨74843828647835014928248429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99791771530446686570997905 74843828647835014928248429)
  ·
    refine ⟨28066435742938130598093161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74843828647835014928248429 28066435742938130598093161)
    ·
      refine ⟨21049826807203597948569871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28066435742938130598093161 21049826807203597948569871)
      ·
        refine ⟨31574740210805396922854807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21049826807203597948569871 31574740210805396922854807)
        ·
          refine ⟨47362110316208095384282211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31574740210805396922854807 47362110316208095384282211)
          ·
            refine ⟨71043165474312143076423317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47362110316208095384282211 71043165474312143076423317)
            ·
              refine ⟨3330148381608381706707343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71043165474312143076423317 3330148381608381706707343)
              ·
                refine ⟨4995222572412572560061015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330148381608381706707343 4995222572412572560061015)
                ·
                  refine ⟨7492833858618858840091523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995222572412572560061015 7492833858618858840091523)
                  ·
                    refine ⟨11239250787928288260137285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7492833858618858840091523 11239250787928288260137285)
                    ·
                      refine ⟨2107359522736554048775741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11239250787928288260137285 2107359522736554048775741)
                      ·
                        rfl

theorem cell23_4104068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_4104068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104068 prefixEnd_4104068 := by exact prefixLift 4104068
  have htrace : WordTrace (prefixWord ++ tailWord_4104068) baseStart_4104068 baseEnd_4104068 := by
    simpa [prefixWord, tailWord_4104068, baseEnd_4104068] using wordTrace_append hprefix tailTrace_4104068
  have hstable : (prefixWord ++ tailWord_4104068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104068).length < 2 ^ (prefixWord ++ tailWord_4104068).sum := by decide
  have hdescent : baseEnd_4104068 < baseStart_4104068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104085 : List Nat := [1, 3, 2, 1, 1, 3, 1, 6, 1, 2, 2]
def baseStart_4104085 : Nat := 118140960795 + 4104085 * 2 ^ 59
def prefixEnd_4104085 : Nat := 4983230072969 + 3 ^ 40 * 4104085 * 2
def baseEnd_4104085 : Nat := 2107368251907680482263163

theorem tailTrace_4104085 : CollatzResearch.WordTrace tailWord_4104085 prefixEnd_4104085 2107368251907680482263163 := by
  unfold tailWord_4104085
  simp only [CollatzResearch.WordTrace]
  refine ⟨149688277336608441759865709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99792184891072294506577139 149688277336608441759865709)
  ·
    refine ⟨56133104001228165659949641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149688277336608441759865709 56133104001228165659949641)
    ·
      refine ⟨42099828000921124244962231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56133104001228165659949641 42099828000921124244962231)
      ·
        refine ⟨63149742001381686367443347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42099828000921124244962231 63149742001381686367443347)
        ·
          refine ⟨94724613002072529551165021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63149742001381686367443347 94724613002072529551165021)
          ·
            refine ⟨35521729875777198581686883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94724613002072529551165021 35521729875777198581686883)
            ·
              refine ⟨53282594813665797872530325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35521729875777198581686883 53282594813665797872530325)
              ·
                refine ⟨2497621631890584275274859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53282594813665797872530325 2497621631890584275274859)
                ·
                  refine ⟨3746432447835876412912289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497621631890584275274859 3746432447835876412912289)
                  ·
                    refine ⟨2809824335876907309684217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3746432447835876412912289 2809824335876907309684217)
                    ·
                      refine ⟨2107368251907680482263163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809824335876907309684217 2107368251907680482263163)
                      ·
                        rfl

theorem cell23_4104085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_4104085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104085 prefixEnd_4104085 := by exact prefixLift 4104085
  have htrace : WordTrace (prefixWord ++ tailWord_4104085) baseStart_4104085 baseEnd_4104085 := by
    simpa [prefixWord, tailWord_4104085, baseEnd_4104085] using wordTrace_append hprefix tailTrace_4104085
  have hstable : (prefixWord ++ tailWord_4104085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104085).length < 2 ^ (prefixWord ++ tailWord_4104085).sum := by decide
  have hdescent : baseEnd_4104085 < baseStart_4104085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104088 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4104088 : Nat := 118140960795 + 4104088 * 2 ^ 59
def prefixEnd_4104088 : Nat := 4983230072969 + 3 ^ 40 * 4104088 * 2
def baseEnd_4104088 : Nat := 2107369792349643970525649

theorem tailTrace_4104088 : CollatzResearch.WordTrace tailWord_4104088 prefixEnd_4104088 2107369792349643970525649 := by
  unfold tailWord_4104088
  simp only [CollatzResearch.WordTrace]
  refine ⟨74844193377798786636112459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99792257837065048848149945 74844193377798786636112459)
  ·
    refine ⟨112266290066698179954168689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74844193377798786636112459 112266290066698179954168689)
    ·
      refine ⟨84199717550023634965626517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112266290066698179954168689 84199717550023634965626517)
      ·
        refine ⟨3946861760157357889013743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84199717550023634965626517 3946861760157357889013743)
        ·
          refine ⟨5920292640236036833520615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3946861760157357889013743 5920292640236036833520615)
          ·
            refine ⟨8880438960354055250280923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920292640236036833520615 8880438960354055250280923)
            ·
              refine ⟨13320658440531082875421385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8880438960354055250280923 13320658440531082875421385)
              ·
                refine ⟨9990493830398312156566039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13320658440531082875421385 9990493830398312156566039)
                ·
                  refine ⟨14985740745597468234849059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9990493830398312156566039 14985740745597468234849059)
                  ·
                    refine ⟨22478611118396202352273589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14985740745597468234849059 22478611118396202352273589)
                    ·
                      refine ⟨2107369792349643970525649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22478611118396202352273589 2107369792349643970525649)
                      ·
                        rfl

theorem cell23_4104088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4104088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104088 prefixEnd_4104088 := by exact prefixLift 4104088
  have htrace : WordTrace (prefixWord ++ tailWord_4104088) baseStart_4104088 baseEnd_4104088 := by
    simpa [prefixWord, tailWord_4104088, baseEnd_4104088] using wordTrace_append hprefix tailTrace_4104088
  have hstable : (prefixWord ++ tailWord_4104088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104088).length < 2 ^ (prefixWord ++ tailWord_4104088).sum := by decide
  have hdescent : baseEnd_4104088 < baseStart_4104088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104095 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 2, 4]
def baseStart_4104095 : Nat := 118140960795 + 4104095 * 2 ^ 59
def prefixEnd_4104095 : Nat := 4983230072969 + 3 ^ 40 * 4104095 * 2
def baseEnd_4104095 : Nat := 702457795571408481046039

theorem tailTrace_4104095 : CollatzResearch.WordTrace tailWord_4104095 prefixEnd_4104095 702457795571408481046039 := by
  unfold tailWord_4104095
  simp only [CollatzResearch.WordTrace]
  refine ⟨149688642066572213467729739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99792428044381475645153159 149688642066572213467729739)
  ·
    refine ⟨224532963099858320201594609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149688642066572213467729739 224532963099858320201594609)
    ·
      refine ⟨168399722324893740151195957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224532963099858320201594609 168399722324893740151195957)
      ·
        refine ⟨15787473967958788139174621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168399722324893740151195957 15787473967958788139174621)
        ·
          refine ⟨5920302737984545552190483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15787473967958788139174621 5920302737984545552190483)
          ·
            refine ⟨8880454106976818328285725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920302737984545552190483 8880454106976818328285725)
            ·
              refine ⟨3330170290116306873107147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8880454106976818328285725 3330170290116306873107147)
              ·
                refine ⟨4995255435174460309660721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330170290116306873107147 4995255435174460309660721)
                ·
                  refine ⟨3746441576380845232245541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4995255435174460309660721 3746441576380845232245541)
                  ·
                    refine ⟨702457795571408481046039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3746441576380845232245541 702457795571408481046039)
                    ·
                      rfl

theorem cell23_4104095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 4].length) (baseStart_4104095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104095 prefixEnd_4104095 := by exact prefixLift 4104095
  have htrace : WordTrace (prefixWord ++ tailWord_4104095) baseStart_4104095 baseEnd_4104095 := by
    simpa [prefixWord, tailWord_4104095, baseEnd_4104095] using wordTrace_append hprefix tailTrace_4104095
  have hstable : (prefixWord ++ tailWord_4104095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104095).length < 2 ^ (prefixWord ++ tailWord_4104095).sum := by decide
  have hdescent : baseEnd_4104095 < baseStart_4104095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104128 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 1, 3, 2]
def baseStart_4104128 : Nat := 118140960795 + 4104128 * 2 ^ 59
def prefixEnd_4104128 : Nat := 4983230072969 + 3 ^ 40 * 4104128 * 2
def baseEnd_4104128 : Nat := 2107390331575823814025465

theorem tailTrace_4104128 : CollatzResearch.WordTrace tailWord_4104128 prefixEnd_4104128 2107390331575823814025465 := by
  unfold tailWord_4104128
  simp only [CollatzResearch.WordTrace]
  refine ⟨74844922837726330051840519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99793230450301773402454025 74844922837726330051840519)
  ·
    refine ⟨112267384256589495077760779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74844922837726330051840519 112267384256589495077760779)
    ·
      refine ⟨168401076384884242616641169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112267384256589495077760779 168401076384884242616641169)
      ·
        refine ⟨126300807288663181962480877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168401076384884242616641169 126300807288663181962480877)
        ·
          refine ⟨47362802733248693235930329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126300807288663181962480877 47362802733248693235930329)
          ·
            refine ⟨35522102049936519926947747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47362802733248693235930329 35522102049936519926947747)
            ·
              refine ⟨53283153074904779890421621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35522102049936519926947747 53283153074904779890421621)
              ·
                refine ⟨4995295600772323114727027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53283153074904779890421621 4995295600772323114727027)
                ·
                  refine ⟨7492943401158484672090541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995295600772323114727027 7492943401158484672090541)
                  ·
                    refine ⟨2809853775434431752033953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7492943401158484672090541 2809853775434431752033953)
                    ·
                      refine ⟨2107390331575823814025465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809853775434431752033953 2107390331575823814025465)
                      ·
                        rfl

theorem cell23_4104128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_4104128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104128 prefixEnd_4104128 := by exact prefixLift 4104128
  have htrace : WordTrace (prefixWord ++ tailWord_4104128) baseStart_4104128 baseEnd_4104128 := by
    simpa [prefixWord, tailWord_4104128, baseEnd_4104128] using wordTrace_append hprefix tailTrace_4104128
  have hstable : (prefixWord ++ tailWord_4104128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104128).length < 2 ^ (prefixWord ++ tailWord_4104128).sum := by decide
  have hdescent : baseEnd_4104128 < baseStart_4104128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104156 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4104156 : Nat := 118140960795 + 4104156 * 2 ^ 59
def prefixEnd_4104156 : Nat := 4983230072969 + 3 ^ 40 * 4104156 * 2
def baseEnd_4104156 : Nat := 2107404709034149704475337

theorem tailTrace_4104156 : CollatzResearch.WordTrace tailWord_4104156 prefixEnd_4104156 2107404709034149704475337 := by
  unfold tailWord_4104156
  simp only [CollatzResearch.WordTrace]
  refine ⟨74845433459675610442850161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99793911279567480590466881 74845433459675610442850161)
  ·
    refine ⟨56134075094756707832137621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74845433459675610442850161 56134075094756707832137621)
    ·
      refine ⟨2631284770066720679631451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56134075094756707832137621 2631284770066720679631451)
      ·
        refine ⟨3946927155100081019447177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631284770066720679631451 3946927155100081019447177)
        ·
          refine ⟨2960195366325060764585383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3946927155100081019447177 2960195366325060764585383)
          ·
            refine ⟨4440293049487591146878075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960195366325060764585383 4440293049487591146878075)
            ·
              refine ⟨6660439574231386720317113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4440293049487591146878075 6660439574231386720317113)
              ·
                refine ⟨4995329680673540040237835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6660439574231386720317113 4995329680673540040237835)
                ·
                  refine ⟨7492994521010310060356753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995329680673540040237835 7492994521010310060356753)
                  ·
                    refine ⟨5619745890757732545267565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7492994521010310060356753 5619745890757732545267565)
                    ·
                      refine ⟨2107404709034149704475337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5619745890757732545267565 2107404709034149704475337)
                      ·
                        rfl

theorem cell23_4104156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4104156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104156 prefixEnd_4104156 := by exact prefixLift 4104156
  have htrace : WordTrace (prefixWord ++ tailWord_4104156) baseStart_4104156 baseEnd_4104156 := by
    simpa [prefixWord, tailWord_4104156, baseEnd_4104156] using wordTrace_append hprefix tailTrace_4104156
  have hstable : (prefixWord ++ tailWord_4104156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104156).length < 2 ^ (prefixWord ++ tailWord_4104156).sum := by decide
  have hdescent : baseEnd_4104156 < baseStart_4104156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104162 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4104162 : Nat := 118140960795 + 4104162 * 2 ^ 59
def prefixEnd_4104162 : Nat := 4983230072969 + 3 ^ 40 * 4104162 * 2
def baseEnd_4104162 : Nat := 2107407789918076681000309

theorem tailTrace_4104162 : CollatzResearch.WordTrace tailWord_4104162 prefixEnd_4104162 2107407789918076681000309 := by
  unfold tailWord_4104162
  simp only [CollatzResearch.WordTrace]
  refine ⟨37422771439332370977604685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99794057171552989273612493 37422771439332370977604685)
  ·
    refine ⟨14033539289749639116601757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37422771439332370977604685 14033539289749639116601757)
    ·
      refine ⟨5262577233656114668725659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14033539289749639116601757 5262577233656114668725659)
      ·
        refine ⟨7893865850484172003088489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5262577233656114668725659 7893865850484172003088489)
        ·
          refine ⟨5920399387863129002316367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7893865850484172003088489 5920399387863129002316367)
          ·
            refine ⟨8880599081794693503474551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920399387863129002316367 8880599081794693503474551)
            ·
              refine ⟨13320898622692040255211827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8880599081794693503474551 13320898622692040255211827)
              ·
                refine ⟨19981347934038060382817741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13320898622692040255211827 19981347934038060382817741)
                ·
                  refine ⟨7493005475264272643556653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19981347934038060382817741 7493005475264272643556653)
                  ·
                    refine ⟨2809877053224102241333745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7493005475264272643556653 2809877053224102241333745)
                    ·
                      refine ⟨2107407789918076681000309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2809877053224102241333745 2107407789918076681000309)
                      ·
                        rfl

theorem cell23_4104162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4104162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104162 prefixEnd_4104162 := by exact prefixLift 4104162
  have htrace : WordTrace (prefixWord ++ tailWord_4104162) baseStart_4104162 baseEnd_4104162 := by
    simpa [prefixWord, tailWord_4104162, baseEnd_4104162] using wordTrace_append hprefix tailTrace_4104162
  have hstable : (prefixWord ++ tailWord_4104162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104162).length < 2 ^ (prefixWord ++ tailWord_4104162).sum := by decide
  have hdescent : baseEnd_4104162 < baseStart_4104162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104164 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 9]
def baseStart_4104164 : Nat := 118140960795 + 4104164 * 2 ^ 59
def prefixEnd_4104164 : Nat := 4983230072969 + 3 ^ 40 * 4104164 * 2
def baseEnd_4104164 : Nat := 234156535208820630352811

theorem tailTrace_4104164 : CollatzResearch.WordTrace tailWord_4104164 prefixEnd_4104164 234156535208820630352811 := by
  unfold tailWord_4104164
  simp only [CollatzResearch.WordTrace]
  refine ⟨74845579351661119125995773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99794105802214825501327697 74845579351661119125995773)
  ·
    refine ⟨28067092256872919672248415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74845579351661119125995773 28067092256872919672248415)
    ·
      refine ⟨42100638385309379508372623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28067092256872919672248415 42100638385309379508372623)
      ·
        refine ⟨63150957577964069262558935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42100638385309379508372623 63150957577964069262558935)
        ·
          refine ⟨94726436366946103893838403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63150957577964069262558935 94726436366946103893838403)
          ·
            refine ⟨142089654550419155840757605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94726436366946103893838403 142089654550419155840757605)
            ·
              refine ⟨26641810228203591720142051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142089654550419155840757605 26641810228203591720142051)
              ·
                refine ⟨39962715342305387580213077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26641810228203591720142051 39962715342305387580213077)
                ·
                  refine ⟨234156535208820630352811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39962715342305387580213077 234156535208820630352811)
                  ·
                    rfl

theorem cell23_4104164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_4104164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104164 prefixEnd_4104164 := by exact prefixLift 4104164
  have htrace : WordTrace (prefixWord ++ tailWord_4104164) baseStart_4104164 baseEnd_4104164 := by
    simpa [prefixWord, tailWord_4104164, baseEnd_4104164] using wordTrace_append hprefix tailTrace_4104164
  have hstable : (prefixWord ++ tailWord_4104164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104164).length < 2 ^ (prefixWord ++ tailWord_4104164).sum := by decide
  have hdescent : baseEnd_4104164 < baseStart_4104164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104228 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_4104228 : Nat := 118140960795 + 4104228 * 2 ^ 59
def prefixEnd_4104228 : Nat := 4983230072969 + 3 ^ 40 * 4104228 * 2
def baseEnd_4104228 : Nat := 702480559880424474258335

theorem tailTrace_4104228 : CollatzResearch.WordTrace tailWord_4104228 prefixEnd_4104228 702480559880424474258335 := by
  unfold tailWord_4104228
  simp only [CollatzResearch.WordTrace]
  refine ⟨74846746487545188591160669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99795661983393584788214225 74846746487545188591160669)
  ·
    refine ⟨28067529932829445721685251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74846746487545188591160669 28067529932829445721685251)
    ·
      refine ⟨42101294899244168582527877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28067529932829445721685251 42101294899244168582527877)
      ·
        refine ⟨7893992793608281609223977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42101294899244168582527877 7893992793608281609223977)
        ·
          refine ⟨5920494595206211206917983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7893992793608281609223977 5920494595206211206917983)
          ·
            refine ⟨8880741892809316810376975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920494595206211206917983 8880741892809316810376975)
            ·
              refine ⟨13321112839213975215565463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8880741892809316810376975 13321112839213975215565463)
              ·
                refine ⟨19981669258820962823348195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13321112839213975215565463 19981669258820962823348195)
                ·
                  refine ⟨29972503888231444235022293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19981669258820962823348195 29972503888231444235022293)
                  ·
                    refine ⟨702480559880424474258335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29972503888231444235022293 702480559880424474258335)
                    ·
                      rfl

theorem cell23_4104228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_4104228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104228 prefixEnd_4104228 := by exact prefixLift 4104228
  have htrace : WordTrace (prefixWord ++ tailWord_4104228) baseStart_4104228 baseEnd_4104228 := by
    simpa [prefixWord, tailWord_4104228, baseEnd_4104228] using wordTrace_append hprefix tailTrace_4104228
  have hstable : (prefixWord ++ tailWord_4104228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104228).length < 2 ^ (prefixWord ++ tailWord_4104228).sum := by decide
  have hdescent : baseEnd_4104228 < baseStart_4104228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104232 : List Nat := [2, 1, 5, 3, 1, 1, 2, 3, 5]
def baseStart_4104232 : Nat := 118140960795 + 4104232 * 2 ^ 59
def prefixEnd_4104232 : Nat := 4983230072969 + 3 ^ 40 * 4104232 * 2
def baseEnd_4104232 : Nat := 234160414840432378569443

theorem tailTrace_4104232 : CollatzResearch.WordTrace tailWord_4104232 prefixEnd_4104232 234160414840432378569443 := by
  unfold tailWord_4104232
  simp only [CollatzResearch.WordTrace]
  refine ⟨74846819433537942932733475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99795759244717257243644633 74846819433537942932733475)
  ·
    refine ⟨112270229150306914399100213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74846819433537942932733475 112270229150306914399100213)
    ·
      refine ⟨10525333982841273224915645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112270229150306914399100213 10525333982841273224915645)
      ·
        refine ⟨3947000243565477459343367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10525333982841273224915645 3947000243565477459343367)
        ·
          refine ⟨5920500365348216189015051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3947000243565477459343367 5920500365348216189015051)
          ·
            refine ⟨8880750548022324283522577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920500365348216189015051 8880750548022324283522577)
            ·
              refine ⟨6660562911016743212641933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8880750548022324283522577 6660562911016743212641933)
              ·
                refine ⟨2497711091631278704740725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6660562911016743212641933 2497711091631278704740725)
                ·
                  refine ⟨234160414840432378569443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2497711091631278704740725 234160414840432378569443)
                  ·
                    rfl

theorem cell23_4104232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 5].length) (baseStart_4104232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104232 prefixEnd_4104232 := by exact prefixLift 4104232
  have htrace : WordTrace (prefixWord ++ tailWord_4104232) baseStart_4104232 baseEnd_4104232 := by
    simpa [prefixWord, tailWord_4104232, baseEnd_4104232] using wordTrace_append hprefix tailTrace_4104232
  have hstable : (prefixWord ++ tailWord_4104232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104232).length < 2 ^ (prefixWord ++ tailWord_4104232).sum := by decide
  have hdescent : baseEnd_4104232 < baseStart_4104232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104281 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 3]
def baseStart_4104281 : Nat := 118140960795 + 4104281 * 2 ^ 59
def prefixEnd_4104281 : Nat := 4983230072969 + 3 ^ 40 * 4104281 * 2
def baseEnd_4104281 : Nat := 2107468894115961715412261

theorem tailTrace_4104281 : CollatzResearch.WordTrace tailWord_4104281 prefixEnd_4104281 2107468894115961715412261 := by
  unfold tailWord_4104281
  simp only [CollatzResearch.WordTrace]
  refine ⟨149695426043898367234000697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99796950695932244822667131 149695426043898367234000697)
  ·
    refine ⟨112271569532923775425500523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149695426043898367234000697 112271569532923775425500523)
    ·
      refine ⟨168407354299385663138250785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112271569532923775425500523 168407354299385663138250785)
      ·
        refine ⟨126305515724539247353688089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168407354299385663138250785 126305515724539247353688089)
        ·
          refine ⟨94729136793404435515266067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126305515724539247353688089 94729136793404435515266067)
          ·
            refine ⟨142093705190106653272899101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94729136793404435515266067 142093705190106653272899101)
            ·
              refine ⟨53285139446289994977337163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142093705190106653272899101 53285139446289994977337163)
              ·
                refine ⟨79927709169434992466005745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53285139446289994977337163 79927709169434992466005745)
                ·
                  refine ⟨59945781877076244349504309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79927709169434992466005745 59945781877076244349504309)
                  ·
                    refine ⟨5619917050975897907766029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59945781877076244349504309 5619917050975897907766029)
                    ·
                      refine ⟨2107468894115961715412261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5619917050975897907766029 2107468894115961715412261)
                      ·
                        rfl

theorem cell23_4104281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_4104281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104281 prefixEnd_4104281 := by exact prefixLift 4104281
  have htrace : WordTrace (prefixWord ++ tailWord_4104281) baseStart_4104281 baseEnd_4104281 := by
    simpa [prefixWord, tailWord_4104281, baseEnd_4104281] using wordTrace_append hprefix tailTrace_4104281
  have hstable : (prefixWord ++ tailWord_4104281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104281).length < 2 ^ (prefixWord ++ tailWord_4104281).sum := by decide
  have hdescent : baseEnd_4104281 < baseStart_4104281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104285 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4104285 : Nat := 118140960795 + 4104285 * 2 ^ 59
def prefixEnd_4104285 : Nat := 4983230072969 + 3 ^ 40 * 4104285 * 2
def baseEnd_4104285 : Nat := 2107470948038579699762243

theorem tailTrace_4104285 : CollatzResearch.WordTrace tailWord_4104285 prefixEnd_4104285 2107470948038579699762243 := by
  unfold tailWord_4104285
  simp only [CollatzResearch.WordTrace]
  refine ⟨149695571935883875917146309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99797047957255917278097539 149695571935883875917146309)
  ·
    refine ⟨28067919737978226734464933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149695571935883875917146309 28067919737978226734464933)
    ·
      refine ⟨5262734950870917512712175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28067919737978226734464933 5262734950870917512712175)
      ·
        refine ⟨7894102426306376269068263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5262734950870917512712175 7894102426306376269068263)
        ·
          refine ⟨11841153639459564403602395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7894102426306376269068263 11841153639459564403602395)
          ·
            refine ⟨17761730459189346605403593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11841153639459564403602395 17761730459189346605403593)
            ·
              refine ⟨13321297844392009954052695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17761730459189346605403593 13321297844392009954052695)
              ·
                refine ⟨19981946766588014931079043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13321297844392009954052695 19981946766588014931079043)
                ·
                  refine ⟨29972920149882022396618565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19981946766588014931079043 29972920149882022396618565)
                  ·
                    refine ⟨5619922528102879199365981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29972920149882022396618565 5619922528102879199365981)
                    ·
                      refine ⟨2107470948038579699762243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5619922528102879199365981 2107470948038579699762243)
                      ·
                        rfl

theorem cell23_4104285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4104285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104285 prefixEnd_4104285 := by exact prefixLift 4104285
  have htrace : WordTrace (prefixWord ++ tailWord_4104285) baseStart_4104285 baseEnd_4104285 := by
    simpa [prefixWord, tailWord_4104285, baseEnd_4104285] using wordTrace_append hprefix tailTrace_4104285
  have hstable : (prefixWord ++ tailWord_4104285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104285).length < 2 ^ (prefixWord ++ tailWord_4104285).sum := by decide
  have hdescent : baseEnd_4104285 < baseStart_4104285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104348 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_4104348 : Nat := 118140960795 + 4104348 * 2 ^ 59
def prefixEnd_4104348 : Nat := 4983230072969 + 3 ^ 40 * 4104348 * 2
def baseEnd_4104348 : Nat := 702501099106604317758151

theorem tailTrace_4104348 : CollatzResearch.WordTrace tailWord_4104348 prefixEnd_4104348 702501099106604317758151 := by
  unfold tailWord_4104348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74848934867327818838344849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99798579823103758451126465 74848934867327818838344849)
  ·
    refine ⟨56136701150495864128758637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74848934867327818838344849 56136701150495864128758637)
    ·
      refine ⟨21051262931435949048284489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56136701150495864128758637 21051262931435949048284489)
      ·
        refine ⟨15788447198576961786213367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21051262931435949048284489 15788447198576961786213367)
        ·
          refine ⟨23682670797865442679320051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15788447198576961786213367 23682670797865442679320051)
          ·
            refine ⟨35524006196798164018980077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23682670797865442679320051 35524006196798164018980077)
            ·
              refine ⟨13321502323799311507117529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35524006196798164018980077 13321502323799311507117529)
              ·
                refine ⟨9991126742849483630338147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13321502323799311507117529 9991126742849483630338147)
                ·
                  refine ⟨14986690114274225445507221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9991126742849483630338147 14986690114274225445507221)
                  ·
                    refine ⟨702501099106604317758151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14986690114274225445507221 702501099106604317758151)
                    ·
                      rfl

theorem cell23_4104348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_4104348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104348 prefixEnd_4104348 := by exact prefixLift 4104348
  have htrace : WordTrace (prefixWord ++ tailWord_4104348) baseStart_4104348 baseEnd_4104348 := by
    simpa [prefixWord, tailWord_4104348, baseEnd_4104348] using wordTrace_append hprefix tailTrace_4104348
  have hstable : (prefixWord ++ tailWord_4104348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104348).length < 2 ^ (prefixWord ++ tailWord_4104348).sum := by decide
  have hdescent : baseEnd_4104348 < baseStart_4104348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104406 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_4104406 : Nat := 118140960795 + 4104406 * 2 ^ 59
def prefixEnd_4104406 : Nat := 4983230072969 + 3 ^ 40 * 4104406 * 2
def baseEnd_4104406 : Nat := 2107533079197773726349187

theorem tailTrace_4104406 : CollatzResearch.WordTrace tailWord_4104406 prefixEnd_4104406 2107533079197773726349187 := by
  unfold tailWord_4104406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9356249073027844598893817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99799990112297009054867381 9356249073027844598893817)
  ·
    refine ⟨7017186804770883449170363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9356249073027844598893817 7017186804770883449170363)
    ·
      refine ⟨10525780207156325173755545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7017186804770883449170363 10525780207156325173755545)
      ·
        refine ⟨7894335155367243880316659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10525780207156325173755545 7894335155367243880316659)
        ·
          refine ⟨11841502733050865820474989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7894335155367243880316659 11841502733050865820474989)
          ·
            refine ⟨4440563524894074682678121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11841502733050865820474989 4440563524894074682678121)
            ·
              refine ⟨3330422643670556012008591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440563524894074682678121 3330422643670556012008591)
              ·
                refine ⟨4995633965505834018012887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330422643670556012008591 4995633965505834018012887)
                ·
                  refine ⟨7493450948258751027019331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995633965505834018012887 7493450948258751027019331)
                  ·
                    refine ⟨11240176422388126540528997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7493450948258751027019331 11240176422388126540528997)
                    ·
                      refine ⟨2107533079197773726349187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11240176422388126540528997 2107533079197773726349187)
                      ·
                        rfl

theorem cell23_4104406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_4104406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104406 prefixEnd_4104406 := by exact prefixLift 4104406
  have htrace : WordTrace (prefixWord ++ tailWord_4104406) baseStart_4104406 baseEnd_4104406 := by
    simpa [prefixWord, tailWord_4104406, baseEnd_4104406] using wordTrace_append hprefix tailTrace_4104406
  have hstable : (prefixWord ++ tailWord_4104406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104406).length < 2 ^ (prefixWord ++ tailWord_4104406).sum := by decide
  have hdescent : baseEnd_4104406 < baseStart_4104406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104448 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3]
def baseStart_4104448 : Nat := 118140960795 + 4104448 * 2 ^ 59
def prefixEnd_4104448 : Nat := 4983230072969 + 3 ^ 40 * 4104448 * 2
def baseEnd_4104448 : Nat := 2107554645385262562023993

theorem tailTrace_4104448 : CollatzResearch.WordTrace tailWord_4104448 prefixEnd_4104448 2107554645385262562023993 := by
  unfold tailWord_4104448
  simp only [CollatzResearch.WordTrace]
  refine ⟨74850758517146677377664999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99801011356195569836886665 74850758517146677377664999)
  ·
    refine ⟨112276137775720016066497499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74850758517146677377664999 112276137775720016066497499)
    ·
      refine ⟨168414206663580024099746249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112276137775720016066497499 168414206663580024099746249)
      ·
        refine ⟨126310654997685018074809687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168414206663580024099746249 126310654997685018074809687)
        ·
          refine ⟨189465982496527527112214531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126310654997685018074809687 189465982496527527112214531)
          ·
            refine ⟨284198973744791290668321797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189465982496527527112214531 284198973744791290668321797)
            ·
              refine ⟨53287307577148367000310337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284198973744791290668321797 53287307577148367000310337)
              ·
                refine ⟨39965480682861275250232753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53287307577148367000310337 39965480682861275250232753)
                ·
                  refine ⟨29974110512145956437674565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39965480682861275250232753 29974110512145956437674565)
                  ·
                    refine ⟨5620145721027366832063981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29974110512145956437674565 5620145721027366832063981)
                    ·
                      refine ⟨2107554645385262562023993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5620145721027366832063981 2107554645385262562023993)
                      ·
                        rfl

theorem cell23_4104448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_4104448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104448 prefixEnd_4104448 := by exact prefixLift 4104448
  have htrace : WordTrace (prefixWord ++ tailWord_4104448) baseStart_4104448 baseEnd_4104448 := by
    simpa [prefixWord, tailWord_4104448, baseEnd_4104448] using wordTrace_append hprefix tailTrace_4104448
  have hstable : (prefixWord ++ tailWord_4104448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104448).length < 2 ^ (prefixWord ++ tailWord_4104448).sum := by decide
  have hdescent : baseEnd_4104448 < baseStart_4104448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104458 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_4104458 : Nat := 118140960795 + 4104458 * 2 ^ 59
def prefixEnd_4104458 : Nat := 4983230072969 + 3 ^ 40 * 4104458 * 2
def baseEnd_4104458 : Nat := 2107559780191807522898947

theorem tailTrace_4104458 : CollatzResearch.WordTrace tailWord_4104458 prefixEnd_4104458 2107559780191807522898947 := by
  unfold tailWord_4104458
  simp only [CollatzResearch.WordTrace]
  refine ⟨37425470441064281615798507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99801254509504750975462685 37425470441064281615798507)
  ·
    refine ⟨56138205661596422423697761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37425470441064281615798507 56138205661596422423697761)
    ·
      refine ⟨42103654246197316817773321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56138205661596422423697761 42103654246197316817773321)
      ·
        refine ⟨31577740684647987613329991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42103654246197316817773321 31577740684647987613329991)
        ·
          refine ⟨47366611026971981419994987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31577740684647987613329991 47366611026971981419994987)
          ·
            refine ⟨71049916540457972129992481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47366611026971981419994987 71049916540457972129992481)
            ·
              refine ⟨53287437405343479097494361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71049916540457972129992481 53287437405343479097494361)
              ·
                refine ⟨39965578054007609323120771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53287437405343479097494361 39965578054007609323120771)
                ·
                  refine ⟨59948367081011413984681157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39965578054007609323120771 59948367081011413984681157)
                  ·
                    refine ⟨11240318827689640122127717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59948367081011413984681157 11240318827689640122127717)
                    ·
                      refine ⟨2107559780191807522898947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11240318827689640122127717 2107559780191807522898947)
                      ·
                        rfl

theorem cell23_4104458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_4104458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104458 prefixEnd_4104458 := by exact prefixLift 4104458
  have htrace : WordTrace (prefixWord ++ tailWord_4104458) baseStart_4104458 baseEnd_4104458 := by
    simpa [prefixWord, tailWord_4104458, baseEnd_4104458] using wordTrace_append hprefix tailTrace_4104458
  have hstable : (prefixWord ++ tailWord_4104458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104458).length < 2 ^ (prefixWord ++ tailWord_4104458).sum := by decide
  have hdescent : baseEnd_4104458 < baseStart_4104458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104462 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_4104462 : Nat := 118140960795 + 4104462 * 2 ^ 59
def prefixEnd_4104462 : Nat := 4983230072969 + 3 ^ 40 * 4104462 * 2
def baseEnd_4104462 : Nat := 2107561834114425507248929

theorem tailTrace_4104462 : CollatzResearch.WordTrace tailWord_4104462 prefixEnd_4104462 2107561834114425507248929 := by
  unfold tailWord_4104462
  simp only [CollatzResearch.WordTrace]
  refine ⟨18712753457030329393292455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99801351770828423430893093 18712753457030329393292455)
  ·
    refine ⟨28069130185545494089938683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18712753457030329393292455 28069130185545494089938683)
    ·
      refine ⟨42103695278318241134908025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28069130185545494089938683 42103695278318241134908025)
      ·
        refine ⟨31577771458738680851181019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42103695278318241134908025 31577771458738680851181019)
        ·
          refine ⟨47366657188108021276771529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31577771458738680851181019 47366657188108021276771529)
          ·
            refine ⟨35524992891081015957578647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47366657188108021276771529 35524992891081015957578647)
            ·
              refine ⟨53287489336621523936367971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35524992891081015957578647 53287489336621523936367971)
              ·
                refine ⟨79931234004932285904551957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53287489336621523936367971 79931234004932285904551957)
                ·
                  refine ⟨3746776593981200901775873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79931234004932285904551957 3746776593981200901775873)
                  ·
                    refine ⟨2810082445485900676331905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3746776593981200901775873 2810082445485900676331905)
                    ·
                      refine ⟨2107561834114425507248929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810082445485900676331905 2107561834114425507248929)
                      ·
                        rfl

theorem cell23_4104462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_4104462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104462 prefixEnd_4104462 := by exact prefixLift 4104462
  have htrace : WordTrace (prefixWord ++ tailWord_4104462) baseStart_4104462 baseEnd_4104462 := by
    simpa [prefixWord, tailWord_4104462, baseEnd_4104462] using wordTrace_append hprefix tailTrace_4104462
  have hstable : (prefixWord ++ tailWord_4104462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104462).length < 2 ^ (prefixWord ++ tailWord_4104462).sum := by decide
  have hdescent : baseEnd_4104462 < baseStart_4104462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104508 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_4104508 : Nat := 118140960795 + 4104508 * 2 ^ 59
def prefixEnd_4104508 : Nat := 4983230072969 + 3 ^ 40 * 4104508 * 2
def baseEnd_4104508 : Nat := 2107585454224532327273717

theorem tailTrace_4104508 : CollatzResearch.WordTrace tailWord_4104508 prefixEnd_4104508 2107585454224532327273717 := by
  unfold tailWord_4104508
  simp only [CollatzResearch.WordTrace]
  refine ⟨74851852707037992501257089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99802470276050656668342785 74851852707037992501257089)
  ·
    refine ⟨56138889530278494375942817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74851852707037992501257089 56138889530278494375942817)
    ·
      refine ⟨42104167147708870781957113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56138889530278494375942817 42104167147708870781957113)
      ·
        refine ⟨31578125360781653086467835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42104167147708870781957113 31578125360781653086467835)
        ·
          refine ⟨47367188041172479629701753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31578125360781653086467835 47367188041172479629701753)
          ·
            refine ⟨35525391030879359722276315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47367188041172479629701753 35525391030879359722276315)
            ·
              refine ⟨53288086546319039583414473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35525391030879359722276315 53288086546319039583414473)
              ·
                refine ⟨39966064909739279687560855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53288086546319039583414473 39966064909739279687560855)
                ·
                  refine ⟨59949097364608919531341283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39966064909739279687560855 59949097364608919531341283)
                  ·
                    refine ⟨89923646046913379297011925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59949097364608919531341283 89923646046913379297011925)
                    ·
                      refine ⟨2107585454224532327273717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89923646046913379297011925 2107585454224532327273717)
                      ·
                        rfl

theorem cell23_4104508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_4104508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104508 prefixEnd_4104508 := by exact prefixLift 4104508
  have htrace : WordTrace (prefixWord ++ tailWord_4104508) baseStart_4104508 baseEnd_4104508 := by
    simpa [prefixWord, tailWord_4104508, baseEnd_4104508] using wordTrace_append hprefix tailTrace_4104508
  have hstable : (prefixWord ++ tailWord_4104508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104508).length < 2 ^ (prefixWord ++ tailWord_4104508).sum := by decide
  have hdescent : baseEnd_4104508 < baseStart_4104508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104535 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_4104535 : Nat := 118140960795 + 4104535 * 2 ^ 59
def prefixEnd_4104535 : Nat := 4983230072969 + 3 ^ 40 * 4104535 * 2
def baseEnd_4104535 : Nat := 2107599318202203721636093

theorem tailTrace_4104535 : CollatzResearch.WordTrace tailWord_4104535 prefixEnd_4104535 2107599318202203721636093 := by
  unfold tailWord_4104535
  simp only [CollatzResearch.WordTrace]
  refine ⟨149704690184978168613747059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99803126789985445742498039 149704690184978168613747059)
  ·
    refine ⟨224557035277467252920620589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149704690184978168613747059 224557035277467252920620589)
    ·
      refine ⟨84208888229050219845232721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224557035277467252920620589 84208888229050219845232721)
      ·
        refine ⟨63156666171787664883924541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84208888229050219845232721 63156666171787664883924541)
        ·
          refine ⟨23683749814420374331471703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63156666171787664883924541 23683749814420374331471703)
          ·
            refine ⟨35525624721630561497207555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23683749814420374331471703 35525624721630561497207555)
            ·
              refine ⟨53288437082445842245811333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35525624721630561497207555 53288437082445842245811333)
              ·
                refine ⟨9991581952958595421089625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53288437082445842245811333 9991581952958595421089625)
                ·
                  refine ⟨7493686464718946565817219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9991581952958595421089625 7493686464718946565817219)
                  ·
                    refine ⟨11240529697078419848725829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7493686464718946565817219 11240529697078419848725829)
                    ·
                      refine ⟨2107599318202203721636093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11240529697078419848725829 2107599318202203721636093)
                      ·
                        rfl

theorem cell23_4104535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_4104535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104535 prefixEnd_4104535 := by exact prefixLift 4104535
  have htrace : WordTrace (prefixWord ++ tailWord_4104535) baseStart_4104535 baseEnd_4104535 := by
    simpa [prefixWord, tailWord_4104535, baseEnd_4104535] using wordTrace_append hprefix tailTrace_4104535
  have hstable : (prefixWord ++ tailWord_4104535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104535).length < 2 ^ (prefixWord ++ tailWord_4104535).sum := by decide
  have hdescent : baseEnd_4104535 < baseStart_4104535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104538 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_4104538 : Nat := 118140960795 + 4104538 * 2 ^ 59
def prefixEnd_4104538 : Nat := 4983230072969 + 3 ^ 40 * 4104538 * 2
def baseEnd_4104538 : Nat := 2107600858644167209898579

theorem tailTrace_4104538 : CollatzResearch.WordTrace tailWord_4104538 prefixEnd_4104538 2107600858644167209898579 := by
  unfold tailWord_4104538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37426199900991825031526567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99803199735978200084070845 37426199900991825031526567)
  ·
    refine ⟨56139299851487737547289851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37426199900991825031526567 56139299851487737547289851)
    ·
      refine ⟨84208949777231606320934777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56139299851487737547289851 84208949777231606320934777)
      ·
        refine ⟨63156712332923704740701083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84208949777231606320934777 63156712332923704740701083)
        ·
          refine ⟨94735068499385557111051625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63156712332923704740701083 94735068499385557111051625)
          ·
            refine ⟨71051301374539167833288719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94735068499385557111051625 71051301374539167833288719)
            ·
              refine ⟨106576952061808751749933079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71051301374539167833288719 106576952061808751749933079)
              ·
                refine ⟨159865428092713127624899619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106576952061808751749933079 159865428092713127624899619)
                ·
                  refine ⟨239798142139069691437349429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159865428092713127624899619 239798142139069691437349429)
                  ·
                    refine ⟨22481075825537783572251509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 239798142139069691437349429 22481075825537783572251509)
                    ·
                      refine ⟨2107600858644167209898579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22481075825537783572251509 2107600858644167209898579)
                      ·
                        rfl

theorem cell23_4104538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_4104538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104538 prefixEnd_4104538 := by exact prefixLift 4104538
  have htrace : WordTrace (prefixWord ++ tailWord_4104538) baseStart_4104538 baseEnd_4104538 := by
    simpa [prefixWord, tailWord_4104538, baseEnd_4104538] using wordTrace_append hprefix tailTrace_4104538
  have hstable : (prefixWord ++ tailWord_4104538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104538).length < 2 ^ (prefixWord ++ tailWord_4104538).sum := by decide
  have hdescent : baseEnd_4104538 < baseStart_4104538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104552 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_4104552 : Nat := 118140960795 + 4104552 * 2 ^ 59
def prefixEnd_4104552 : Nat := 4983230072969 + 3 ^ 40 * 4104552 * 2
def baseEnd_4104552 : Nat := 2107608047373330155123515

theorem tailTrace_4104552 : CollatzResearch.WordTrace tailWord_4104552 prefixEnd_4104552 2107608047373330155123515 := by
  unfold tailWord_4104552
  simp only [CollatzResearch.WordTrace]
  refine ⟨74852655112958290258557955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99803540150611053678077273 74852655112958290258557955)
  ·
    refine ⟨112278982669437435387836933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74852655112958290258557955 112278982669437435387836933)
    ·
      refine ⟨21052309250519519135219425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112278982669437435387836933 21052309250519519135219425)
      ·
        refine ⟨15789231937889639351414569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21052309250519519135219425 15789231937889639351414569)
        ·
          refine ⟨11841923953417229513560927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15789231937889639351414569 11841923953417229513560927)
          ·
            refine ⟨17762885930125844270341391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11841923953417229513560927 17762885930125844270341391)
            ·
              refine ⟨26644328895188766405512087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17762885930125844270341391 26644328895188766405512087)
              ·
                refine ⟨39966493342783149608268131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26644328895188766405512087 39966493342783149608268131)
                ·
                  refine ⟨59949740014174724412402197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39966493342783149608268131 59949740014174724412402197)
                  ·
                    refine ⟨2810144063164440206831353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59949740014174724412402197 2810144063164440206831353)
                    ·
                      refine ⟨2107608047373330155123515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810144063164440206831353 2107608047373330155123515)
                      ·
                        rfl

theorem cell23_4104552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_4104552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104552 prefixEnd_4104552 := by exact prefixLift 4104552
  have htrace : WordTrace (prefixWord ++ tailWord_4104552) baseStart_4104552 baseEnd_4104552 := by
    simpa [prefixWord, tailWord_4104552, baseEnd_4104552] using wordTrace_append hprefix tailTrace_4104552
  have hstable : (prefixWord ++ tailWord_4104552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104552).length < 2 ^ (prefixWord ++ tailWord_4104552).sum := by decide
  have hdescent : baseEnd_4104552 < baseStart_4104552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104562 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_4104562 : Nat := 118140960795 + 4104562 * 2 ^ 59
def prefixEnd_4104562 : Nat := 4983230072969 + 3 ^ 40 * 4104562 * 2
def baseEnd_4104562 : Nat := 702537727393291705332823

theorem tailTrace_4104562 : CollatzResearch.WordTrace tailWord_4104562 prefixEnd_4104562 702537727393291705332823 := by
  unfold tailWord_4104562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37426418738970088056244985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99803783303920234816653293 37426418738970088056244985)
  ·
    refine ⟨28069814054227566042183739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37426418738970088056244985 28069814054227566042183739)
    ·
      refine ⟨42104721081341349063275609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28069814054227566042183739 42104721081341349063275609)
      ·
        refine ⟨31578540811006011797456707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42104721081341349063275609 31578540811006011797456707)
        ·
          refine ⟨47367811216509017696185061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31578540811006011797456707 47367811216509017696185061)
          ·
            refine ⟨8881464603095440818034699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47367811216509017696185061 8881464603095440818034699)
            ·
              refine ⟨13322196904643161227052049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881464603095440818034699 13322196904643161227052049)
              ·
                refine ⟨9991647678482370920289037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13322196904643161227052049 9991647678482370920289037)
                ·
                  refine ⟨3746867879430889095108389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9991647678482370920289037 3746867879430889095108389)
                  ·
                    refine ⟨702537727393291705332823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3746867879430889095108389 702537727393291705332823)
                    ·
                      rfl

theorem cell23_4104562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_4104562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104562 prefixEnd_4104562 := by exact prefixLift 4104562
  have htrace : WordTrace (prefixWord ++ tailWord_4104562) baseStart_4104562 baseEnd_4104562 := by
    simpa [prefixWord, tailWord_4104562, baseEnd_4104562] using wordTrace_append hprefix tailTrace_4104562
  have hstable : (prefixWord ++ tailWord_4104562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104562).length < 2 ^ (prefixWord ++ tailWord_4104562).sum := by decide
  have hdescent : baseEnd_4104562 < baseStart_4104562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104566 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_4104566 : Nat := 118140960795 + 4104566 * 2 ^ 59
def prefixEnd_4104566 : Nat := 4983230072969 + 3 ^ 40 * 4104566 * 2
def baseEnd_4104566 : Nat := 702538412034164366782817

theorem tailTrace_4104566 : CollatzResearch.WordTrace tailWord_4104566 prefixEnd_4104566 702538412034164366782817 := by
  unfold tailWord_4104566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9356613802991616306757847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99803880565243907272083701 9356613802991616306757847)
  ·
    refine ⟨14034920704487424460136771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9356613802991616306757847 14034920704487424460136771)
    ·
      refine ⟨21052381056731136690205157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14034920704487424460136771 21052381056731136690205157)
      ·
        refine ⟨3947321448137088129413467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21052381056731136690205157 3947321448137088129413467)
        ·
          refine ⟨5920982172205632194120201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3947321448137088129413467 5920982172205632194120201)
          ·
            refine ⟨4440736629154224145590151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5920982172205632194120201 4440736629154224145590151)
            ·
              refine ⟨6661104943731336218385227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4440736629154224145590151 6661104943731336218385227)
              ·
                refine ⟨9991657415597004327577841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661104943731336218385227 9991657415597004327577841)
                ·
                  refine ⟨7493743061697753245683381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9991657415597004327577841 7493743061697753245683381)
                  ·
                    refine ⟨702538412034164366782817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7493743061697753245683381 702538412034164366782817)
                    ·
                      rfl

theorem cell23_4104566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_4104566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104566 prefixEnd_4104566 := by exact prefixLift 4104566
  have htrace : WordTrace (prefixWord ++ tailWord_4104566) baseStart_4104566 baseEnd_4104566 := by
    simpa [prefixWord, tailWord_4104566, baseEnd_4104566] using wordTrace_append hprefix tailTrace_4104566
  have hstable : (prefixWord ++ tailWord_4104566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104566).length < 2 ^ (prefixWord ++ tailWord_4104566).sum := by decide
  have hdescent : baseEnd_4104566 < baseStart_4104566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104612 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_4104612 : Nat := 118140960795 + 4104612 * 2 ^ 59
def prefixEnd_4104612 : Nat := 4983230072969 + 3 ^ 40 * 4104612 * 2
def baseEnd_4104612 : Nat := 2107638856212599920373239

theorem tailTrace_4104612 : CollatzResearch.WordTrace tailWord_4104612 prefixEnd_4104612 2107638856212599920373239 := by
  unfold tailWord_4104612
  simp only [CollatzResearch.WordTrace]
  refine ⟨74853749302849605382150045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99804999070466140509533393 74853749302849605382150045)
  ·
    refine ⟨28070155988568602018306267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74853749302849605382150045 28070155988568602018306267)
    ·
      refine ⟨42105233982852903027459401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28070155988568602018306267 42105233982852903027459401)
      ·
        refine ⟨31578925487139677270594551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42105233982852903027459401 31578925487139677270594551)
        ·
          refine ⟨47368388230709515905891827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31578925487139677270594551 47368388230709515905891827)
          ·
            refine ⟨71052582346064273858837741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47368388230709515905891827 71052582346064273858837741)
            ·
              refine ⟨26644718379774102697064153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71052582346064273858837741 26644718379774102697064153)
              ·
                refine ⟨19983538784830577022798115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26644718379774102697064153 19983538784830577022798115)
                ·
                  refine ⟨29975308177245865534197173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19983538784830577022798115 29975308177245865534197173)
                  ·
                    refine ⟨2810185141616799893830985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29975308177245865534197173 2810185141616799893830985)
                    ·
                      refine ⟨2107638856212599920373239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810185141616799893830985 2107638856212599920373239)
                      ·
                        rfl

theorem cell23_4104612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_4104612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104612 prefixEnd_4104612 := by exact prefixLift 4104612
  have htrace : WordTrace (prefixWord ++ tailWord_4104612) baseStart_4104612 baseEnd_4104612 := by
    simpa [prefixWord, tailWord_4104612, baseEnd_4104612] using wordTrace_append hprefix tailTrace_4104612
  have hstable : (prefixWord ++ tailWord_4104612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104612).length < 2 ^ (prefixWord ++ tailWord_4104612).sum := by decide
  have hdescent : baseEnd_4104612 < baseStart_4104612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104665 : List Nat := [1, 2, 1, 2, 4, 1, 4, 8]
def baseStart_4104665 : Nat := 118140960795 + 4104665 * 2 ^ 59
def prefixEnd_4104665 : Nat := 4983230072969 + 3 ^ 40 * 4104665 * 2
def baseEnd_4104665 : Nat := 78061706321751415296685

theorem tailTrace_4104665 : CollatzResearch.WordTrace tailWord_4104665 prefixEnd_4104665 78061706321751415296685 := by
  unfold tailWord_4104665
  simp only [CollatzResearch.WordTrace]
  refine ⟨149709431674507200815979449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99806287783004800543986299 149709431674507200815979449)
  ·
    refine ⟨112282073755880400611984587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149709431674507200815979449 112282073755880400611984587)
    ·
      refine ⟨168423110633820600917976881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112282073755880400611984587 168423110633820600917976881)
      ·
        refine ⟨126317332975365450688482661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168423110633820600917976881 126317332975365450688482661)
        ·
          refine ⟨23684499932881022004090499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126317332975365450688482661 23684499932881022004090499)
          ·
            refine ⟨35526749899321533006135749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23684499932881022004090499 35526749899321533006135749)
            ·
              refine ⟨6661265606122787438650453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35526749899321533006135749 6661265606122787438650453)
              ·
                refine ⟨78061706321751415296685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6661265606122787438650453 78061706321751415296685)
                ·
                  rfl

theorem cell23_4104665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 8].length) (baseStart_4104665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104665 prefixEnd_4104665 := by exact prefixLift 4104665
  have htrace : WordTrace (prefixWord ++ tailWord_4104665) baseStart_4104665 baseEnd_4104665 := by
    simpa [prefixWord, tailWord_4104665, baseEnd_4104665] using wordTrace_append hprefix tailTrace_4104665
  have hstable : (prefixWord ++ tailWord_4104665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104665).length < 2 ^ (prefixWord ++ tailWord_4104665).sum := by decide
  have hdescent : baseEnd_4104665 < baseStart_4104665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104669 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_4104669 : Nat := 118140960795 + 4104669 * 2 ^ 59
def prefixEnd_4104669 : Nat := 4983230072969 + 3 ^ 40 * 4104669 * 2
def baseEnd_4104669 : Nat := 702556041536635399120159

theorem tailTrace_4104669 : CollatzResearch.WordTrace tailWord_4104669 prefixEnd_4104669 702556041536635399120159 := by
  unfold tailWord_4104669
  simp only [CollatzResearch.WordTrace]
  refine ⟨149709577566492709499125061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99806385044328472999416707 149709577566492709499125061)
  ·
    refine ⟨28070545793717383031085949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149709577566492709499125061 28070545793717383031085949)
    ·
      refine ⟨10526454672644018636657231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28070545793717383031085949 10526454672644018636657231)
      ·
        refine ⟨15789682008966027954985847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10526454672644018636657231 15789682008966027954985847)
        ·
          refine ⟨23684523013449041932478771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15789682008966027954985847 23684523013449041932478771)
          ·
            refine ⟨35526784520173562898718157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23684523013449041932478771 35526784520173562898718157)
            ·
              refine ⟨13322544195065086087019309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35526784520173562898718157 13322544195065086087019309)
              ·
                refine ⟨4995954073149407282632241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13322544195065086087019309 4995954073149407282632241)
                ·
                  refine ⟨3746965554862055461974181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4995954073149407282632241 3746965554862055461974181)
                  ·
                    refine ⟨702556041536635399120159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3746965554862055461974181 702556041536635399120159)
                    ·
                      rfl

theorem cell23_4104669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_4104669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104669 prefixEnd_4104669 := by exact prefixLift 4104669
  have htrace : WordTrace (prefixWord ++ tailWord_4104669) baseStart_4104669 baseEnd_4104669 := by
    simpa [prefixWord, tailWord_4104669, baseEnd_4104669] using wordTrace_append hprefix tailTrace_4104669
  have hstable : (prefixWord ++ tailWord_4104669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104669).length < 2 ^ (prefixWord ++ tailWord_4104669).sum := by decide
  have hdescent : baseEnd_4104669 < baseStart_4104669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104693 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4104693 : Nat := 118140960795 + 4104693 * 2 ^ 59
def prefixEnd_4104693 : Nat := 4983230072969 + 3 ^ 40 * 4104693 * 2
def baseEnd_4104693 : Nat := 2107680448145614103460367

theorem tailTrace_4104693 : CollatzResearch.WordTrace tailWord_4104693 prefixEnd_4104693 2107680448145614103460367 := by
  unfold tailWord_4104693
  simp only [CollatzResearch.WordTrace]
  refine ⟨149710452918405761597998733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99806968612270507731999155 149710452918405761597998733)
  ·
    refine ⟨56141419844402160599249525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149710452918405761597998733 56141419844402160599249525)
    ·
      refine ⟨5263258110412702556179643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56141419844402160599249525 5263258110412702556179643)
      ·
        refine ⟨7894887165619053834269465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263258110412702556179643 7894887165619053834269465)
        ·
          refine ⟨5921165374214290375702099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7894887165619053834269465 5921165374214290375702099)
          ·
            refine ⟨8881748061321435563553149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921165374214290375702099 8881748061321435563553149)
            ·
              refine ⟨3330655522995538336332431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8881748061321435563553149 3330655522995538336332431)
              ·
                refine ⟨4995983284493307504498647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330655522995538336332431 4995983284493307504498647)
                ·
                  refine ⟨7493974926739961256747971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995983284493307504498647 7493974926739961256747971)
                  ·
                    refine ⟨11240962390109941885121957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7493974926739961256747971 11240962390109941885121957)
                    ·
                      refine ⟨2107680448145614103460367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11240962390109941885121957 2107680448145614103460367)
                      ·
                        rfl

theorem cell23_4104693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4104693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104693 prefixEnd_4104693 := by exact prefixLift 4104693
  have htrace : WordTrace (prefixWord ++ tailWord_4104693) baseStart_4104693 baseEnd_4104693 := by
    simpa [prefixWord, tailWord_4104693, baseEnd_4104693] using wordTrace_append hprefix tailTrace_4104693
  have hstable : (prefixWord ++ tailWord_4104693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104693).length < 2 ^ (prefixWord ++ tailWord_4104693).sum := by decide
  have hdescent : baseEnd_4104693 < baseStart_4104693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104709 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 3]
def baseStart_4104709 : Nat := 118140960795 + 4104709 * 2 ^ 59
def prefixEnd_4104709 : Nat := 4983230072969 + 3 ^ 40 * 4104709 * 2
def baseEnd_4104709 : Nat := 2107688663836086040860293

theorem tailTrace_4104709 : CollatzResearch.WordTrace tailWord_4104709 prefixEnd_4104709 2107688663836086040860293 := by
  unfold tailWord_4104709
  simp only [CollatzResearch.WordTrace]
  refine ⟨149711036486347796330581181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99807357657565197553720787 149711036486347796330581181)
  ·
    refine ⟨56141638682380423623967943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149711036486347796330581181 56141638682380423623967943)
    ·
      refine ⟨84212458023570635435951915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56141638682380423623967943 84212458023570635435951915)
      ·
        refine ⟨126318687035355953153927873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84212458023570635435951915 126318687035355953153927873)
        ·
          refine ⟨94739015276516964865445905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126318687035355953153927873 94739015276516964865445905)
          ·
            refine ⟨71054261457387723649084429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94739015276516964865445905 71054261457387723649084429)
            ·
              refine ⟨26645348046520396368406661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71054261457387723649084429 26645348046520396368406661)
              ·
                refine ⟨4996002758722574319076249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26645348046520396368406661 4996002758722574319076249)
                ·
                  refine ⟨3747002069041930739307187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4996002758722574319076249 3747002069041930739307187)
                  ·
                    refine ⟨5620503103562896108960781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3747002069041930739307187 5620503103562896108960781)
                    ·
                      refine ⟨2107688663836086040860293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5620503103562896108960781 2107688663836086040860293)
                      ·
                        rfl

theorem cell23_4104709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_4104709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104709 prefixEnd_4104709 := by exact prefixLift 4104709
  have htrace : WordTrace (prefixWord ++ tailWord_4104709) baseStart_4104709 baseEnd_4104709 := by
    simpa [prefixWord, tailWord_4104709, baseEnd_4104709] using wordTrace_append hprefix tailTrace_4104709
  have hstable : (prefixWord ++ tailWord_4104709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104709).length < 2 ^ (prefixWord ++ tailWord_4104709).sum := by decide
  have hdescent : baseEnd_4104709 < baseStart_4104709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104755 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 9]
def baseStart_4104755 : Nat := 118140960795 + 4104755 * 2 ^ 59
def prefixEnd_4104755 : Nat := 4983230072969 + 3 ^ 40 * 4104755 * 2
def baseEnd_4104755 : Nat := 234190253771799206765009

theorem tailTrace_4104755 : CollatzResearch.WordTrace tailWord_4104755 prefixEnd_4104755 234190253771799206765009 := by
  unfold tailWord_4104755
  simp only [CollatzResearch.WordTrace]
  refine ⟨149712714244181146186755719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99808476162787430791170479 149712714244181146186755719)
  ·
    refine ⟨224569071366271719280133579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149712714244181146186755719 224569071366271719280133579)
    ·
      refine ⟨336853607049407578920200369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224569071366271719280133579 336853607049407578920200369)
      ·
        refine ⟨252640205287055684190150277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336853607049407578920200369 252640205287055684190150277)
        ·
          refine ⟨47370038491322940785653177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252640205287055684190150277 47370038491322940785653177)
          ·
            refine ⟨35527528868492205589239883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47370038491322940785653177 35527528868492205589239883)
            ·
              refine ⟨53291293302738308383859825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35527528868492205589239883 53291293302738308383859825)
              ·
                refine ⟨39968469977053731287894869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53291293302738308383859825 39968469977053731287894869)
                ·
                  refine ⟨234190253771799206765009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39968469977053731287894869 234190253771799206765009)
                  ·
                    rfl

theorem cell23_4104755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 9].length) (baseStart_4104755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104755 prefixEnd_4104755 := by exact prefixLift 4104755
  have htrace : WordTrace (prefixWord ++ tailWord_4104755) baseStart_4104755 baseEnd_4104755 := by
    simpa [prefixWord, tailWord_4104755, baseEnd_4104755] using wordTrace_append hprefix tailTrace_4104755
  have hstable : (prefixWord ++ tailWord_4104755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104755).length < 2 ^ (prefixWord ++ tailWord_4104755).sum := by decide
  have hdescent : baseEnd_4104755 < baseStart_4104755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104762 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_4104762 : Nat := 118140960795 + 4104762 * 2 ^ 59
def prefixEnd_4104762 : Nat := 4983230072969 + 3 ^ 40 * 4104762 * 2
def baseEnd_4104762 : Nat := 2107715878310774333497549

theorem tailTrace_4104762 : CollatzResearch.WordTrace tailWord_4104762 prefixEnd_4104762 2107715878310774333497549 := by
  unfold tailWord_4104762
  simp only [CollatzResearch.WordTrace]
  refine ⟨37428242388788946595565135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99808646370103857588173693 37428242388788946595565135)
  ·
    refine ⟨56142363583183419893347703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37428242388788946595565135 56142363583183419893347703)
    ·
      refine ⟨84213545374775129840021555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56142363583183419893347703 84213545374775129840021555)
      ·
        refine ⟨126320318062162694760032333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84213545374775129840021555 126320318062162694760032333)
        ·
          refine ⟨47370119273311010535012125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126320318062162694760032333 47370119273311010535012125)
          ·
            refine ⟨17763794727491628950629547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47370119273311010535012125 17763794727491628950629547)
            ·
              refine ⟨26645692091237443425944321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17763794727491628950629547 26645692091237443425944321)
              ·
                refine ⟨19984269068428082569458241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26645692091237443425944321 19984269068428082569458241)
                ·
                  refine ⟨14988201801321061927093681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19984269068428082569458241 14988201801321061927093681)
                  ·
                    refine ⟨11241151350990796445320261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14988201801321061927093681 11241151350990796445320261)
                    ·
                      refine ⟨2107715878310774333497549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11241151350990796445320261 2107715878310774333497549)
                      ·
                        rfl

theorem cell23_4104762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_4104762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104762 prefixEnd_4104762 := by exact prefixLift 4104762
  have htrace : WordTrace (prefixWord ++ tailWord_4104762) baseStart_4104762 baseEnd_4104762 := by
    simpa [prefixWord, tailWord_4104762, baseEnd_4104762] using wordTrace_append hprefix tailTrace_4104762
  have hstable : (prefixWord ++ tailWord_4104762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104762).length < 2 ^ (prefixWord ++ tailWord_4104762).sum := by decide
  have hdescent : baseEnd_4104762 < baseStart_4104762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104829 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_4104829 : Nat := 118140960795 + 4104829 * 2 ^ 59
def prefixEnd_4104829 : Nat := 4983230072969 + 3 ^ 40 * 4104829 * 2
def baseEnd_4104829 : Nat := 2107750281514625571359741

theorem tailTrace_4104829 : CollatzResearch.WordTrace tailWord_4104829 prefixEnd_4104829 2107750281514625571359741 := by
  unfold tailWord_4104829
  simp only [CollatzResearch.WordTrace]
  refine ⟨149715413245913056824949541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99810275497275371216633027 149715413245913056824949541)
  ·
    refine ⟨28071639983608698154678039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149715413245913056824949541 28071639983608698154678039)
    ·
      refine ⟨42107459975413047232017059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28071639983608698154678039 42107459975413047232017059)
      ·
        refine ⟨63161189963119570848025589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42107459975413047232017059 63161189963119570848025589)
        ·
          refine ⟨5921361559042459767002399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63161189963119570848025589 5921361559042459767002399)
          ·
            refine ⟨8882042338563689650503599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921361559042459767002399 8882042338563689650503599)
            ·
              refine ⟨13323063507845534475755399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882042338563689650503599 13323063507845534475755399)
              ·
                refine ⟨19984595261768301713633099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13323063507845534475755399 19984595261768301713633099)
                ·
                  refine ⟨29976892892652452570449649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19984595261768301713633099 29976892892652452570449649)
                  ·
                    refine ⟨22482669669489339427837237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29976892892652452570449649 22482669669489339427837237)
                    ·
                      refine ⟨2107750281514625571359741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22482669669489339427837237 2107750281514625571359741)
                      ·
                        rfl

theorem cell23_4104829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_4104829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104829 prefixEnd_4104829 := by exact prefixLift 4104829
  have htrace : WordTrace (prefixWord ++ tailWord_4104829) baseStart_4104829 baseEnd_4104829 := by
    simpa [prefixWord, tailWord_4104829, baseEnd_4104829] using wordTrace_append hprefix tailTrace_4104829
  have hstable : (prefixWord ++ tailWord_4104829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104829).length < 2 ^ (prefixWord ++ tailWord_4104829).sum := by decide
  have hdescent : baseEnd_4104829 < baseStart_4104829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104834 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4104834 : Nat := 118140960795 + 4104834 * 2 ^ 59
def prefixEnd_4104834 : Nat := 4983230072969 + 3 ^ 40 * 4104834 * 2
def baseEnd_4104834 : Nat := 2107752848917898051797219

theorem tailTrace_4104834 : CollatzResearch.WordTrace tailWord_4104834 prefixEnd_4104834 2107752848917898051797219 := by
  unfold tailWord_4104834
  simp only [CollatzResearch.WordTrace]
  refine ⟨37428898902723735669720389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99810397073929961785921037 37428898902723735669720389)
  ·
    refine ⟨7017918544260700438072573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37428898902723735669720389 7017918544260700438072573)
    ·
      refine ⟨2631719454097762664277215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7017918544260700438072573 2631719454097762664277215)
      ·
        refine ⟨3947579181146643996415823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631719454097762664277215 3947579181146643996415823)
        ·
          refine ⟨5921368771719965994623735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3947579181146643996415823 5921368771719965994623735)
          ·
            refine ⟨8882053157579948991935603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921368771719965994623735 8882053157579948991935603)
            ·
              refine ⟨13323079736369923487903405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882053157579948991935603 13323079736369923487903405)
              ·
                refine ⟨4996154901138721307963777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13323079736369923487903405 4996154901138721307963777)
                ·
                  refine ⟨3747116175854040980972833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4996154901138721307963777 3747116175854040980972833)
                  ·
                    refine ⟨2810337131890530735729625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3747116175854040980972833 2810337131890530735729625)
                    ·
                      refine ⟨2107752848917898051797219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810337131890530735729625 2107752848917898051797219)
                      ·
                        rfl

theorem cell23_4104834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4104834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104834 prefixEnd_4104834 := by exact prefixLift 4104834
  have htrace : WordTrace (prefixWord ++ tailWord_4104834) baseStart_4104834 baseEnd_4104834 := by
    simpa [prefixWord, tailWord_4104834, baseEnd_4104834] using wordTrace_append hprefix tailTrace_4104834
  have hstable : (prefixWord ++ tailWord_4104834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104834).length < 2 ^ (prefixWord ++ tailWord_4104834).sum := by decide
  have hdescent : baseEnd_4104834 < baseStart_4104834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104839 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_4104839 : Nat := 118140960795 + 4104839 * 2 ^ 59
def prefixEnd_4104839 : Nat := 4983230072969 + 3 ^ 40 * 4104839 * 2
def baseEnd_4104839 : Nat := 2107755416321170532234695

theorem tailTrace_4104839 : CollatzResearch.WordTrace tailWord_4104839 prefixEnd_4104839 2107755416321170532234695 := by
  unfold tailWord_4104839
  simp only [CollatzResearch.WordTrace]
  refine ⟨149715777975876828532813571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99810518650584552355209047 149715777975876828532813571)
  ·
    refine ⟨224573666963815242799220357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149715777975876828532813571 224573666963815242799220357)
    ·
      refine ⟨42107562555715358024853817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224573666963815242799220357 42107562555715358024853817)
      ·
        refine ⟨31580671916786518518640363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42107562555715358024853817 31580671916786518518640363)
        ·
          refine ⟨47371007875179777777960545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31580671916786518518640363 47371007875179777777960545)
          ·
            refine ⟨35528255906384833333470409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47371007875179777777960545 35528255906384833333470409)
            ·
              refine ⟨26646191929788625000102807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35528255906384833333470409 26646191929788625000102807)
              ·
                refine ⟨39969287894682937500154211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26646191929788625000102807 39969287894682937500154211)
                ·
                  refine ⟨59953931842024406250231317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39969287894682937500154211 59953931842024406250231317)
                  ·
                    refine ⟨2810340555094894042979593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59953931842024406250231317 2810340555094894042979593)
                    ·
                      refine ⟨2107755416321170532234695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810340555094894042979593 2107755416321170532234695)
                      ·
                        rfl

theorem cell23_4104839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_4104839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104839 prefixEnd_4104839 := by exact prefixLift 4104839
  have htrace : WordTrace (prefixWord ++ tailWord_4104839) baseStart_4104839 baseEnd_4104839 := by
    simpa [prefixWord, tailWord_4104839, baseEnd_4104839] using wordTrace_append hprefix tailTrace_4104839
  have hstable : (prefixWord ++ tailWord_4104839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104839).length < 2 ^ (prefixWord ++ tailWord_4104839).sum := by decide
  have hdescent : baseEnd_4104839 < baseStart_4104839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104879 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 6]
def baseStart_4104879 : Nat := 118140960795 + 4104879 * 2 ^ 59
def prefixEnd_4104879 : Nat := 4983230072969 + 3 ^ 40 * 4104879 * 2
def baseEnd_4104879 : Nat := 234197328394150041748279

theorem tailTrace_4104879 : CollatzResearch.WordTrace tailWord_4104879 prefixEnd_4104879 234197328394150041748279 := by
  unfold tailWord_4104879
  simp only [CollatzResearch.WordTrace]
  refine ⟨149717236895731915364269691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99811491263821276909513127 149717236895731915364269691)
  ·
    refine ⟨224575855343597873046404537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149717236895731915364269691 224575855343597873046404537)
    ·
      refine ⟨168431891507698404784803403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224575855343597873046404537 168431891507698404784803403)
      ·
        refine ⟨252647837261547607177205105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168431891507698404784803403 252647837261547607177205105)
        ·
          refine ⟨189485877946160705382903829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252647837261547607177205105 189485877946160705382903829)
          ·
            refine ⟨8882150528726283064823617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189485877946160705382903829 8882150528726283064823617)
            ·
              refine ⟨6661612896544712298617713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882150528726283064823617 6661612896544712298617713)
              ·
                refine ⟨4996209672408534223963285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6661612896544712298617713 4996209672408534223963285)
                ·
                  refine ⟨234197328394150041748279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4996209672408534223963285 234197328394150041748279)
                  ·
                    rfl

theorem cell23_4104879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 6].length) (baseStart_4104879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104879 prefixEnd_4104879 := by exact prefixLift 4104879
  have htrace : WordTrace (prefixWord ++ tailWord_4104879) baseStart_4104879 baseEnd_4104879 := by
    simpa [prefixWord, tailWord_4104879, baseEnd_4104879] using wordTrace_append hprefix tailTrace_4104879
  have hstable : (prefixWord ++ tailWord_4104879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104879).length < 2 ^ (prefixWord ++ tailWord_4104879).sum := by decide
  have hdescent : baseEnd_4104879 < baseStart_4104879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104882 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_4104882 : Nat := 118140960795 + 4104882 * 2 ^ 59
def prefixEnd_4104882 : Nat := 4983230072969 + 3 ^ 40 * 4104882 * 2
def baseEnd_4104882 : Nat := 2107777495989313863996997

theorem tailTrace_4104882 : CollatzResearch.WordTrace tailWord_4104882 prefixEnd_4104882 2107777495989313863996997 := by
  unfold tailWord_4104882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37429336578680261719157225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99811564209814031251085933 37429336578680261719157225)
  ·
    refine ⟨28072002434010196289367919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37429336578680261719157225 28072002434010196289367919)
    ·
      refine ⟨42108003651015294434051879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28072002434010196289367919 42108003651015294434051879)
      ·
        refine ⟨63162005476522941651077819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42108003651015294434051879 63162005476522941651077819)
        ·
          refine ⟨94743008214784412476616729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63162005476522941651077819 94743008214784412476616729)
          ·
            refine ⟨71057256161088309357462547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94743008214784412476616729 71057256161088309357462547)
            ·
              refine ⟨106585884241632464036193821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71057256161088309357462547 106585884241632464036193821)
              ·
                refine ⟨39969706590612174013572683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106585884241632464036193821 39969706590612174013572683)
                ·
                  refine ⟨59954559885918261020359025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39969706590612174013572683 59954559885918261020359025)
                  ·
                    refine ⟨44965919914438695765269269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59954559885918261020359025 44965919914438695765269269)
                    ·
                      refine ⟨2107777495989313863996997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44965919914438695765269269 2107777495989313863996997)
                      ·
                        rfl

theorem cell23_4104882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_4104882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104882 prefixEnd_4104882 := by exact prefixLift 4104882
  have htrace : WordTrace (prefixWord ++ tailWord_4104882) baseStart_4104882 baseEnd_4104882 := by
    simpa [prefixWord, tailWord_4104882, baseEnd_4104882] using wordTrace_append hprefix tailTrace_4104882
  have hstable : (prefixWord ++ tailWord_4104882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104882).length < 2 ^ (prefixWord ++ tailWord_4104882).sum := by decide
  have hdescent : baseEnd_4104882 < baseStart_4104882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104883 : List Nat := [1, 1, 1, 2, 3, 4, 4, 2, 1, 4]
def baseStart_4104883 : Nat := 118140960795 + 4104883 * 2 ^ 59
def prefixEnd_4104883 : Nat := 4983230072969 + 3 ^ 40 * 4104883 * 2
def baseEnd_4104883 : Nat := 702592669823322786694831

theorem tailTrace_4104883 : CollatzResearch.WordTrace tailWord_4104883 prefixEnd_4104883 702592669823322786694831 := by
  unfold tailWord_4104883
  simp only [CollatzResearch.WordTrace]
  refine ⟨149717382787717424047415303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99811588525144949364943535 149717382787717424047415303)
  ·
    refine ⟨224576074181576136071122955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149717382787717424047415303 224576074181576136071122955)
    ·
      refine ⟨336864111272364204106684433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224576074181576136071122955 336864111272364204106684433)
      ·
        refine ⟨252648083454273153080013325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336864111272364204106684433 252648083454273153080013325)
        ·
          refine ⟨94743031295352432405004997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252648083454273153080013325 94743031295352432405004997)
          ·
            refine ⟨17764318367878581075938437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94743031295352432405004997 17764318367878581075938437)
            ·
              refine ⟨3330809693977233951738457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17764318367878581075938437 3330809693977233951738457)
              ·
                refine ⟨2498107270482925463803843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3330809693977233951738457 2498107270482925463803843)
                ·
                  refine ⟨3747160905724388195705765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498107270482925463803843 3747160905724388195705765)
                  ·
                    refine ⟨702592669823322786694831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3747160905724388195705765 702592669823322786694831)
                    ·
                      rfl

theorem cell23_4104883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 4].length) (baseStart_4104883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104883 prefixEnd_4104883 := by exact prefixLift 4104883
  have htrace : WordTrace (prefixWord ++ tailWord_4104883) baseStart_4104883 baseEnd_4104883 := by
    simpa [prefixWord, tailWord_4104883, baseEnd_4104883] using wordTrace_append hprefix tailTrace_4104883
  have hstable : (prefixWord ++ tailWord_4104883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104883).length < 2 ^ (prefixWord ++ tailWord_4104883).sum := by decide
  have hdescent : baseEnd_4104883 < baseStart_4104883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104906 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_4104906 : Nat := 118140960795 + 4104906 * 2 ^ 59
def prefixEnd_4104906 : Nat := 4983230072969 + 3 ^ 40 * 4104906 * 2
def baseEnd_4104906 : Nat := 2107789819525021770096887

theorem tailTrace_4104906 : CollatzResearch.WordTrace tailWord_4104906 prefixEnd_4104906 2107789819525021770096887 := by
  unfold tailWord_4104906
  simp only [CollatzResearch.WordTrace]
  refine ⟨37429555416658524743875643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99812147777756065983668381 37429555416658524743875643)
  ·
    refine ⟨56144333124987787115813465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37429555416658524743875643 56144333124987787115813465)
    ·
      refine ⟨42108249843740840336860099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56144333124987787115813465 42108249843740840336860099)
      ·
        refine ⟨63162374765611260505290149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42108249843740840336860099 63162374765611260505290149)
        ·
          refine ⟨11842945268552111344741903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63162374765611260505290149 11842945268552111344741903)
          ·
            refine ⟨17764417902828167017112855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11842945268552111344741903 17764417902828167017112855)
            ·
              refine ⟨26646626854242250525669283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17764417902828167017112855 26646626854242250525669283)
              ·
                refine ⟨39969940281363375788503925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26646626854242250525669283 39969940281363375788503925)
                ·
                  refine ⟨3747181901377816480172243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39969940281363375788503925 3747181901377816480172243)
                  ·
                    refine ⟨5620772852066724720258365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3747181901377816480172243 5620772852066724720258365)
                    ·
                      refine ⟨2107789819525021770096887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5620772852066724720258365 2107789819525021770096887)
                      ·
                        rfl

theorem cell23_4104906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_4104906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104906 prefixEnd_4104906 := by exact prefixLift 4104906
  have htrace : WordTrace (prefixWord ++ tailWord_4104906) baseStart_4104906 baseEnd_4104906 := by
    simpa [prefixWord, tailWord_4104906, baseEnd_4104906] using wordTrace_append hprefix tailTrace_4104906
  have hstable : (prefixWord ++ tailWord_4104906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104906).length < 2 ^ (prefixWord ++ tailWord_4104906).sum := by decide
  have hdescent : baseEnd_4104906 < baseStart_4104906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104952 : List Nat := [2, 1, 2, 1, 1, 2, 4, 10]
def baseStart_4104952 : Nat := 118140960795 + 4104952 * 2 ^ 59
def prefixEnd_4104952 : Nat := 4983230072969 + 3 ^ 40 * 4104952 * 2
def baseEnd_4104952 : Nat := 78067164430930688523025

theorem tailTrace_4104952 : CollatzResearch.WordTrace tailWord_4104952 prefixEnd_4104952 78067164430930688523025 := by
  unfold tailWord_4104952
  simp only [CollatzResearch.WordTrace]
  refine ⟨74859949712233724415838555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99813266282978299221118073 74859949712233724415838555)
  ·
    refine ⟨112289924568350586623757833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74859949712233724415838555 112289924568350586623757833)
    ·
      refine ⟨84217443426262939967818375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112289924568350586623757833 84217443426262939967818375)
      ·
        refine ⟨126326165139394409951727563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84217443426262939967818375 126326165139394409951727563)
        ·
          refine ⟨189489247709091614927591345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126326165139394409951727563 189489247709091614927591345)
          ·
            refine ⟨142116935781818711195693509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189489247709091614927591345 142116935781818711195693509)
            ·
              refine ⟨26646925459091008349192533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142116935781818711195693509 26646925459091008349192533)
              ·
                refine ⟨78067164430930688523025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26646925459091008349192533 78067164430930688523025)
                ·
                  rfl

theorem cell23_4104952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 10].length) (baseStart_4104952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104952 prefixEnd_4104952 := by exact prefixLift 4104952
  have htrace : WordTrace (prefixWord ++ tailWord_4104952) baseStart_4104952 baseEnd_4104952 := by
    simpa [prefixWord, tailWord_4104952, baseEnd_4104952] using wordTrace_append hprefix tailTrace_4104952
  have hstable : (prefixWord ++ tailWord_4104952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104952).length < 2 ^ (prefixWord ++ tailWord_4104952).sum := by decide
  have hdescent : baseEnd_4104952 < baseStart_4104952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104956 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_4104956 : Nat := 118140960795 + 4104956 * 2 ^ 59
def prefixEnd_4104956 : Nat := 4983230072969 + 3 ^ 40 * 4104956 * 2
def baseEnd_4104956 : Nat := 702605164519248858157219

theorem tailTrace_4104956 : CollatzResearch.WordTrace tailWord_4104956 prefixEnd_4104956 702605164519248858157219 := by
  unfold tailWord_4104956
  simp only [CollatzResearch.WordTrace]
  refine ⟨74860022658226478757411361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99813363544301971676548481 74860022658226478757411361)
  ·
    refine ⟨56145016993669859068058521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74860022658226478757411361 56145016993669859068058521)
    ·
      refine ⟨42108762745252394301043891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56145016993669859068058521 42108762745252394301043891)
      ·
        refine ⟨63163144117878591451565837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42108762745252394301043891 63163144117878591451565837)
        ·
          refine ⟨23686179044204471794337189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63163144117878591451565837 23686179044204471794337189)
          ·
            refine ⟨4441158570788338461438223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23686179044204471794337189 4441158570788338461438223)
            ·
              refine ⟨6661737856182507692157335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441158570788338461438223 6661737856182507692157335)
              ·
                refine ⟨9992606784273761538236003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661737856182507692157335 9992606784273761538236003)
                ·
                  refine ⟨14988910176410642307354005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9992606784273761538236003 14988910176410642307354005)
                  ·
                    refine ⟨702605164519248858157219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14988910176410642307354005 702605164519248858157219)
                    ·
                      rfl

theorem cell23_4104956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_4104956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104956 prefixEnd_4104956 := by exact prefixLift 4104956
  have htrace : WordTrace (prefixWord ++ tailWord_4104956) baseStart_4104956 baseEnd_4104956 := by
    simpa [prefixWord, tailWord_4104956, baseEnd_4104956] using wordTrace_append hprefix tailTrace_4104956
  have hstable : (prefixWord ++ tailWord_4104956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104956).length < 2 ^ (prefixWord ++ tailWord_4104956).sum := by decide
  have hdescent : baseEnd_4104956 < baseStart_4104956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104969 : List Nat := [1, 2, 1, 1, 3, 2, 6, 7]
def baseStart_4104969 : Nat := 118140960795 + 4104969 * 2 ^ 59
def prefixEnd_4104969 : Nat := 4983230072969 + 3 ^ 40 * 4104969 * 2
def baseEnd_4104969 : Nat := 78067487733565000874411

theorem tailTrace_4104969 : CollatzResearch.WordTrace tailWord_4104969 prefixEnd_4104969 78067487733565000874411 := by
  unfold tailWord_4104969
  simp only [CollatzResearch.WordTrace]
  refine ⟨149720519465405860735045961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99813679643603907156697307 149720519465405860735045961)
  ·
    refine ⟨112290389599054395551284471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149720519465405860735045961 112290389599054395551284471)
    ·
      refine ⟨168435584398581593326926707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112290389599054395551284471 168435584398581593326926707)
      ·
        refine ⟨252653376597872389990390061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168435584398581593326926707 252653376597872389990390061)
        ·
          refine ⟨94745016224202146246396273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252653376597872389990390061 94745016224202146246396273)
          ·
            refine ⟨71058762168151609684797205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94745016224202146246396273 71058762168151609684797205)
            ·
              refine ⟨3330879476632106703974869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71058762168151609684797205 3330879476632106703974869)
              ·
                refine ⟨78067487733565000874411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3330879476632106703974869 78067487733565000874411)
                ·
                  rfl

theorem cell23_4104969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 7].length) (baseStart_4104969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104969 prefixEnd_4104969 := by exact prefixLift 4104969
  have htrace : WordTrace (prefixWord ++ tailWord_4104969) baseStart_4104969 baseEnd_4104969 := by
    simpa [prefixWord, tailWord_4104969, baseEnd_4104969] using wordTrace_append hprefix tailTrace_4104969
  have hstable : (prefixWord ++ tailWord_4104969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104969).length < 2 ^ (prefixWord ++ tailWord_4104969).sum := by decide
  have hdescent : baseEnd_4104969 < baseStart_4104969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104979 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 3]
def baseStart_4104979 : Nat := 118140960795 + 4104979 * 2 ^ 59
def prefixEnd_4104979 : Nat := 4983230072969 + 3 ^ 40 * 4104979 * 2
def baseEnd_4104979 : Nat := 2107827303612799984484051

theorem tailTrace_4104979 : CollatzResearch.WordTrace tailWord_4104979 prefixEnd_4104979 2107827303612799984484051 := by
  unfold tailWord_4104979
  simp only [CollatzResearch.WordTrace]
  refine ⟨149720884195369632442909991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99813922796913088295273327 149720884195369632442909991)
  ·
    refine ⟨224581326293054448664364987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149720884195369632442909991 224581326293054448664364987)
    ·
      refine ⟨336871989439581672996547481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224581326293054448664364987 336871989439581672996547481)
      ·
        refine ⟨252653992079686254747410611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336871989439581672996547481 252653992079686254747410611)
        ·
          refine ⟨378980988119529382121115917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252653992079686254747410611 378980988119529382121115917)
          ·
            refine ⟨142117870544823518295418469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378980988119529382121115917 142117870544823518295418469)
            ·
              refine ⟨26647100727154409680390963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142117870544823518295418469 26647100727154409680390963)
              ·
                refine ⟨39970651090731614520586445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26647100727154409680390963 39970651090731614520586445)
                ·
                  refine ⟨14988994159024355445219917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39970651090731614520586445 14988994159024355445219917)
                  ·
                    refine ⟨5620872809634133291957469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14988994159024355445219917 5620872809634133291957469)
                    ·
                      refine ⟨2107827303612799984484051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5620872809634133291957469 2107827303612799984484051)
                      ·
                        rfl

theorem cell23_4104979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_4104979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104979 prefixEnd_4104979 := by exact prefixLift 4104979
  have htrace : WordTrace (prefixWord ++ tailWord_4104979) baseStart_4104979 baseEnd_4104979 := by
    simpa [prefixWord, tailWord_4104979, baseEnd_4104979] using wordTrace_append hprefix tailTrace_4104979
  have hstable : (prefixWord ++ tailWord_4104979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104979).length < 2 ^ (prefixWord ++ tailWord_4104979).sum := by decide
  have hdescent : baseEnd_4104979 < baseStart_4104979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104997 : List Nat := [1, 3, 1, 2, 3, 1, 5, 2, 1, 2, 2]
def baseStart_4104997 : Nat := 118140960795 + 4104997 * 2 ^ 59
def prefixEnd_4104997 : Nat := 4983230072969 + 3 ^ 40 * 4104997 * 2
def baseEnd_4104997 : Nat := 2107836546264580914058969

theorem tailTrace_4104997 : CollatzResearch.WordTrace tailWord_4104997 prefixEnd_4104997 2107836546264580914058969 := by
  unfold tailWord_4104997
  simp only [CollatzResearch.WordTrace]
  refine ⟨149721540709304421517065245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99814360472869614344710163 149721540709304421517065245)
  ·
    refine ⟨56145577765989158068899467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149721540709304421517065245 56145577765989158068899467)
    ·
      refine ⟨84218366648983737103349201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56145577765989158068899467 84218366648983737103349201)
      ·
        refine ⟨63163774986737802827511901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84218366648983737103349201 63163774986737802827511901)
        ·
          refine ⟨23686415620026676060316963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63163774986737802827511901 23686415620026676060316963)
          ·
            refine ⟨35529623430040014090475445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23686415620026676060316963 35529623430040014090475445)
            ·
              refine ⟨3330902196566251320982073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35529623430040014090475445 3330902196566251320982073)
              ·
                refine ⟨2498176647424688490736555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3330902196566251320982073 2498176647424688490736555)
                ·
                  refine ⟨3747264971137032736104833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498176647424688490736555 3747264971137032736104833)
                  ·
                    refine ⟨2810448728352774552078625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3747264971137032736104833 2810448728352774552078625)
                    ·
                      refine ⟨2107836546264580914058969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810448728352774552078625 2107836546264580914058969)
                      ·
                        rfl

theorem cell23_4104997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_4104997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4104997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4104997 prefixEnd_4104997 := by exact prefixLift 4104997
  have htrace : WordTrace (prefixWord ++ tailWord_4104997) baseStart_4104997 baseEnd_4104997 := by
    simpa [prefixWord, tailWord_4104997, baseEnd_4104997] using wordTrace_append hprefix tailTrace_4104997
  have hstable : (prefixWord ++ tailWord_4104997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104997).length < 2 ^ (prefixWord ++ tailWord_4104997).sum := by decide
  have hdescent : baseEnd_4104997 < baseStart_4104997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105023 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 3, 3, 2]
def baseStart_4105023 : Nat := 118140960795 + 4105023 * 2 ^ 59
def prefixEnd_4105023 : Nat := 4983230072969 + 3 ^ 40 * 4105023 * 2
def baseEnd_4105023 : Nat := 2107849896761597812333849

theorem tailTrace_4105023 : CollatzResearch.WordTrace tailWord_4105023 prefixEnd_4105023 2107849896761597812333849 := by
  unfold tailWord_4105023
  simp only [CollatzResearch.WordTrace]
  refine ⟨149722489007210227957511723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99814992671473485305007815 149722489007210227957511723)
  ·
    refine ⟨224583733510815341936267585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149722489007210227957511723 224583733510815341936267585)
    ·
      refine ⟨168437800133111506452200689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224583733510815341936267585 168437800133111506452200689)
      ·
        refine ⟨126328350099833629839150517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168437800133111506452200689 126328350099833629839150517)
        ·
          refine ⟨11843282821859402797420361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126328350099833629839150517 11843282821859402797420361)
          ·
            refine ⟨8882462116394552098065271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843282821859402797420361 8882462116394552098065271)
            ·
              refine ⟨13323693174591828147097907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882462116394552098065271 13323693174591828147097907)
              ·
                refine ⟨19985539761887742220646861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13323693174591828147097907 19985539761887742220646861)
                ·
                  refine ⟨7494577410707903332742573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19985539761887742220646861 7494577410707903332742573)
                  ·
                    refine ⟨2810466529015463749778465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7494577410707903332742573 2810466529015463749778465)
                    ·
                      refine ⟨2107849896761597812333849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810466529015463749778465 2107849896761597812333849)
                      ·
                        rfl

theorem cell23_4105023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_4105023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105023 prefixEnd_4105023 := by exact prefixLift 4105023
  have htrace : WordTrace (prefixWord ++ tailWord_4105023) baseStart_4105023 baseEnd_4105023 := by
    simpa [prefixWord, tailWord_4105023, baseEnd_4105023] using wordTrace_append hprefix tailTrace_4105023
  have hstable : (prefixWord ++ tailWord_4105023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105023).length < 2 ^ (prefixWord ++ tailWord_4105023).sum := by decide
  have hdescent : baseEnd_4105023 < baseStart_4105023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105039 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 3]
def baseStart_4105039 : Nat := 118140960795 + 4105039 * 2 ^ 59
def prefixEnd_4105039 : Nat := 4983230072969 + 3 ^ 40 * 4105039 * 2
def baseEnd_4105039 : Nat := 2107858112452069749733775

theorem tailTrace_4105039 : CollatzResearch.WordTrace tailWord_4105039 prefixEnd_4105039 2107858112452069749733775 := by
  unfold tailWord_4105039
  simp only [CollatzResearch.WordTrace]
  refine ⟨149723072575152262690094171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99815381716768175126729447 149723072575152262690094171)
  ·
    refine ⟨224584608862728394035141257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149723072575152262690094171 224584608862728394035141257)
    ·
      refine ⟨168438456647046295526355943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224584608862728394035141257 168438456647046295526355943)
      ·
        refine ⟨252657684970569443289533915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168438456647046295526355943 252657684970569443289533915)
        ·
          refine ⟨378986527455854164934300873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252657684970569443289533915 378986527455854164934300873)
          ·
            refine ⟨284239895591890623700725655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378986527455854164934300873 284239895591890623700725655)
            ·
              refine ⟨426359843387835935551088483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284239895591890623700725655 426359843387835935551088483)
              ·
                refine ⟨639539765081753903326632725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426359843387835935551088483 639539765081753903326632725)
                ·
                  refine ⟨29978426488207214218435909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 639539765081753903326632725 29978426488207214218435909)
                  ·
                    refine ⟨5620954966538852665956733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29978426488207214218435909 5620954966538852665956733)
                    ·
                      refine ⟨2107858112452069749733775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5620954966538852665956733 2107858112452069749733775)
                      ·
                        rfl

theorem cell23_4105039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_4105039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105039 prefixEnd_4105039 := by exact prefixLift 4105039
  have htrace : WordTrace (prefixWord ++ tailWord_4105039) baseStart_4105039 baseEnd_4105039 := by
    simpa [prefixWord, tailWord_4105039, baseEnd_4105039] using wordTrace_append hprefix tailTrace_4105039
  have hstable : (prefixWord ++ tailWord_4105039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105039).length < 2 ^ (prefixWord ++ tailWord_4105039).sum := by decide
  have hdescent : baseEnd_4105039 < baseStart_4105039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105093 : List Nat := [1, 3, 1, 1, 3, 4, 2, 3, 5]
def baseStart_4105093 : Nat := 118140960795 + 4105093 * 2 ^ 59
def prefixEnd_4105093 : Nat := 4983230072969 + 3 ^ 40 * 4105093 * 2
def baseEnd_4105093 : Nat := 234209537823045837606503

theorem tailTrace_4105093 : CollatzResearch.WordTrace tailWord_4105093 prefixEnd_4105093 234209537823045837606503 := by
  unfold tailWord_4105093
  simp only [CollatzResearch.WordTrace]
  refine ⟨149725042116956629912559933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99816694744637753275039955 149725042116956629912559933)
  ·
    refine ⟨56146890793858736217209975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149725042116956629912559933 56146890793858736217209975)
    ·
      refine ⟨84220336190788104325814963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56146890793858736217209975 84220336190788104325814963)
      ·
        refine ⟨126330504286182156488722445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84220336190788104325814963 126330504286182156488722445)
        ·
          refine ⟨47373939107318308683270917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126330504286182156488722445 47373939107318308683270917)
          ·
            refine ⟨8882613582622182878113297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47373939107318308683270917 8882613582622182878113297)
            ·
              refine ⟨6661960186966637158584973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882613582622182878113297 6661960186966637158584973)
              ·
                refine ⟨2498235070112488934469365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6661960186966637158584973 2498235070112488934469365)
                ·
                  refine ⟨234209537823045837606503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2498235070112488934469365 234209537823045837606503)
                  ·
                    rfl

theorem cell23_4105093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_4105093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105093 prefixEnd_4105093 := by exact prefixLift 4105093
  have htrace : WordTrace (prefixWord ++ tailWord_4105093) baseStart_4105093 baseEnd_4105093 := by
    simpa [prefixWord, tailWord_4105093, baseEnd_4105093] using wordTrace_append hprefix tailTrace_4105093
  have hstable : (prefixWord ++ tailWord_4105093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105093).length < 2 ^ (prefixWord ++ tailWord_4105093).sum := by decide
  have hdescent : baseEnd_4105093 < baseStart_4105093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105099 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 5]
def baseStart_4105099 : Nat := 118140960795 + 4105099 * 2 ^ 59
def prefixEnd_4105099 : Nat := 4983230072969 + 3 ^ 40 * 4105099 * 2
def baseEnd_4105099 : Nat := 2107888921291339514983499

theorem tailTrace_4105099 : CollatzResearch.WordTrace tailWord_4105099 prefixEnd_4105099 2107888921291339514983499 := by
  unfold tailWord_4105099
  simp only [CollatzResearch.WordTrace]
  refine ⟨149725260954934892937278351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99816840636623261958185567 149725260954934892937278351)
  ·
    refine ⟨224587891432402339405917527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149725260954934892937278351 224587891432402339405917527)
    ·
      refine ⟨336881837148603509108876291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224587891432402339405917527 336881837148603509108876291)
      ·
        refine ⟨505322755722905263663314437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336881837148603509108876291 505322755722905263663314437)
        ·
          refine ⟨94748016698044736936871457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505322755722905263663314437 94748016698044736936871457)
          ·
            refine ⟨71061012523533552702653593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94748016698044736936871457 71061012523533552702653593)
            ·
              refine ⟨53295759392650164526990195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71061012523533552702653593 53295759392650164526990195)
              ·
                refine ⟨79943639088975246790485293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53295759392650164526990195 79943639088975246790485293)
                ·
                  refine ⟨29978864658365717546431985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79943639088975246790485293 29978864658365717546431985)
                  ·
                    refine ⟨22484148493774288159823989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29978864658365717546431985 22484148493774288159823989)
                    ·
                      refine ⟨2107888921291339514983499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22484148493774288159823989 2107888921291339514983499)
                      ·
                        rfl

theorem cell23_4105099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_4105099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105099 prefixEnd_4105099 := by exact prefixLift 4105099
  have htrace : WordTrace (prefixWord ++ tailWord_4105099) baseStart_4105099 baseEnd_4105099 := by
    simpa [prefixWord, tailWord_4105099, baseEnd_4105099] using wordTrace_append hprefix tailTrace_4105099
  have hstable : (prefixWord ++ tailWord_4105099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105099).length < 2 ^ (prefixWord ++ tailWord_4105099).sum := by decide
  have hdescent : baseEnd_4105099 < baseStart_4105099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105110 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_4105110 : Nat := 118140960795 + 4105110 * 2 ^ 59
def prefixEnd_4105110 : Nat := 4983230072969 + 3 ^ 40 * 4105110 * 2
def baseEnd_4105110 : Nat := 234210507730948774660661

theorem tailTrace_4105110 : CollatzResearch.WordTrace tailWord_4105110 prefixEnd_4105110 234210507730948774660661 := by
  unfold tailWord_4105110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9357853884868440113495549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99817108105263361210619189 9357853884868440113495549)
  ·
    refine ⟨3509195206825665042560831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9357853884868440113495549 3509195206825665042560831)
    ·
      refine ⟨5263792810238497563841247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3509195206825665042560831 5263792810238497563841247)
      ·
        refine ⟨7895689215357746345761871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263792810238497563841247 7895689215357746345761871)
        ·
          refine ⟨11843533823036619518642807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895689215357746345761871 11843533823036619518642807)
          ·
            refine ⟨17765300734554929277964211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11843533823036619518642807 17765300734554929277964211)
            ·
              refine ⟨26647951101832393916946317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17765300734554929277964211 26647951101832393916946317)
              ·
                refine ⟨9992981663187147718854869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26647951101832393916946317 9992981663187147718854869)
                ·
                  refine ⟨234210507730948774660661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9992981663187147718854869 234210507730948774660661)
                  ·
                    rfl

theorem cell23_4105110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_4105110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105110 prefixEnd_4105110 := by exact prefixLift 4105110
  have htrace : WordTrace (prefixWord ++ tailWord_4105110) baseStart_4105110 baseEnd_4105110 := by
    simpa [prefixWord, tailWord_4105110, baseEnd_4105110] using wordTrace_append hprefix tailTrace_4105110
  have hstable : (prefixWord ++ tailWord_4105110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105110).length < 2 ^ (prefixWord ++ tailWord_4105110).sum := by decide
  have hdescent : baseEnd_4105110 < baseStart_4105110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105139 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 6]
def baseStart_4105139 : Nat := 118140960795 + 4105139 * 2 ^ 59
def prefixEnd_4105139 : Nat := 4983230072969 + 3 ^ 40 * 4105139 * 2
def baseEnd_4105139 : Nat := 2107909460517519358483315

theorem tailTrace_4105139 : CollatzResearch.WordTrace tailWord_4105139 prefixEnd_4105139 2107909460517519358483315 := by
  unfold tailWord_4105139
  simp only [CollatzResearch.WordTrace]
  refine ⟨149726719874789979768734471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99817813249859986512489647 149726719874789979768734471)
  ·
    refine ⟨224590079812184969653101707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149726719874789979768734471 224590079812184969653101707)
    ·
      refine ⟨336885119718277454479652561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224590079812184969653101707 336885119718277454479652561)
      ·
        refine ⟨252663839788708090859739421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336885119718277454479652561 252663839788708090859739421)
        ·
          refine ⟨94748939920765534072402283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252663839788708090859739421 94748939920765534072402283)
          ·
            refine ⟨142123409881148301108603425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94748939920765534072402283 142123409881148301108603425)
            ·
              refine ⟨106592557410861225831452569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142123409881148301108603425 106592557410861225831452569)
              ·
                refine ⟨79944418058145919373589427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106592557410861225831452569 79944418058145919373589427)
                ·
                  refine ⟨119916627087218879060384141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79944418058145919373589427 119916627087218879060384141)
                  ·
                    refine ⟨44968735157707079647644053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119916627087218879060384141 44968735157707079647644053)
                    ·
                      refine ⟨2107909460517519358483315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44968735157707079647644053 2107909460517519358483315)
                      ·
                        rfl

theorem cell23_4105139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_4105139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105139 prefixEnd_4105139 := by exact prefixLift 4105139
  have htrace : WordTrace (prefixWord ++ tailWord_4105139) baseStart_4105139 baseEnd_4105139 := by
    simpa [prefixWord, tailWord_4105139, baseEnd_4105139] using wordTrace_append hprefix tailTrace_4105139
  have hstable : (prefixWord ++ tailWord_4105139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105139).length < 2 ^ (prefixWord ++ tailWord_4105139).sum := by decide
  have hdescent : baseEnd_4105139 < baseStart_4105139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105146 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_4105146 : Nat := 118140960795 + 4105146 * 2 ^ 59
def prefixEnd_4105146 : Nat := 4983230072969 + 3 ^ 40 * 4105146 * 2
def baseEnd_4105146 : Nat := 2107913054882100831095783

theorem tailTrace_4105146 : CollatzResearch.WordTrace tailWord_4105146 prefixEnd_4105146 2107913054882100831095783 := by
  unfold tailWord_4105146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37431743796441154991059823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99817983457176413309492861 37431743796441154991059823)
  ·
    refine ⟨56147615694661732486589735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37431743796441154991059823 56147615694661732486589735)
    ·
      refine ⟨84221423541992598729884603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56147615694661732486589735 84221423541992598729884603)
      ·
        refine ⟨126332135312988898094826905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84221423541992598729884603 126332135312988898094826905)
        ·
          refine ⟨94749101484741673571120179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126332135312988898094826905 94749101484741673571120179)
          ·
            refine ⟨142123652227112510356680269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94749101484741673571120179 142123652227112510356680269)
            ·
              refine ⟨53296369585167191383755101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142123652227112510356680269 53296369585167191383755101)
              ·
                refine ⟨19986138594437696768908163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53296369585167191383755101 19986138594437696768908163)
                ·
                  refine ⟨29979207891656545153362245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19986138594437696768908163 29979207891656545153362245)
                  ·
                    refine ⟨5621101479685602216255421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29979207891656545153362245 5621101479685602216255421)
                    ·
                      refine ⟨2107913054882100831095783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5621101479685602216255421 2107913054882100831095783)
                      ·
                        rfl

theorem cell23_4105146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_4105146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105146 prefixEnd_4105146 := by exact prefixLift 4105146
  have htrace : WordTrace (prefixWord ++ tailWord_4105146) baseStart_4105146 baseEnd_4105146 := by
    simpa [prefixWord, tailWord_4105146, baseEnd_4105146] using wordTrace_append hprefix tailTrace_4105146
  have hstable : (prefixWord ++ tailWord_4105146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105146).length < 2 ^ (prefixWord ++ tailWord_4105146).sum := by decide
  have hdescent : baseEnd_4105146 < baseStart_4105146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105163 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 3]
def baseStart_4105163 : Nat := 118140960795 + 4105163 * 2 ^ 59
def prefixEnd_4105163 : Nat := 4983230072969 + 3 ^ 40 * 4105163 * 2
def baseEnd_4105163 : Nat := 2107921784053227264583205

theorem tailTrace_4105163 : CollatzResearch.WordTrace tailWord_4105163 prefixEnd_4105163 2107921784053227264583205 := by
  unfold tailWord_4105163
  simp only [CollatzResearch.WordTrace]
  refine ⟨149727595226703031867608143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99818396817802021245072095 149727595226703031867608143)
  ·
    refine ⟨224591392840054547801412215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149727595226703031867608143 224591392840054547801412215)
    ·
      refine ⟨336887089260081821702118323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224591392840054547801412215 336887089260081821702118323)
      ·
        refine ⟨505330633890122732553177485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336887089260081821702118323 505330633890122732553177485)
        ·
          refine ⟨189498987708796024707441557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505330633890122732553177485 189498987708796024707441557)
          ·
            refine ⟨8882765048849813658161323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189498987708796024707441557 8882765048849813658161323)
            ·
              refine ⟨13324147573274720487241985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882765048849813658161323 13324147573274720487241985)
              ·
                refine ⟨9993110679956040365431489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13324147573274720487241985 9993110679956040365431489)
                ·
                  refine ⟨7494833009967030274073617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9993110679956040365431489 7494833009967030274073617)
                  ·
                    refine ⟨5621124757475272705555213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7494833009967030274073617 5621124757475272705555213)
                    ·
                      refine ⟨2107921784053227264583205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5621124757475272705555213 2107921784053227264583205)
                      ·
                        rfl

theorem cell23_4105163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 3].length) (baseStart_4105163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105163 prefixEnd_4105163 := by exact prefixLift 4105163
  have htrace : WordTrace (prefixWord ++ tailWord_4105163) baseStart_4105163 baseEnd_4105163 := by
    simpa [prefixWord, tailWord_4105163, baseEnd_4105163] using wordTrace_append hprefix tailTrace_4105163
  have hstable : (prefixWord ++ tailWord_4105163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105163).length < 2 ^ (prefixWord ++ tailWord_4105163).sum := by decide
  have hdescent : baseEnd_4105163 < baseStart_4105163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105166 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_4105166 : Nat := 118140960795 + 4105166 * 2 ^ 59
def prefixEnd_4105166 : Nat := 4983230072969 + 3 ^ 40 * 4105166 * 2
def baseEnd_4105166 : Nat := 234213702721687861427299

theorem tailTrace_4105166 : CollatzResearch.WordTrace tailWord_4105166 prefixEnd_4105166 234213702721687861427299 := by
  unfold tailWord_4105166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715963080711520422495919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99818469763794775586644901 18715963080711520422495919)
  ·
    refine ⟨28073944621067280633743879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18715963080711520422495919 28073944621067280633743879)
    ·
      refine ⟨42110916931600920950615819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28073944621067280633743879 42110916931600920950615819)
      ·
        refine ⟨63166375397401381425923729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42110916931600920950615819 63166375397401381425923729)
        ·
          refine ⟨47374781548051036069442797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63166375397401381425923729 47374781548051036069442797)
          ·
            refine ⟨17765543080519138526041049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47374781548051036069442797 17765543080519138526041049)
            ·
              refine ⟨13324157310389353894530787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17765543080519138526041049 13324157310389353894530787)
              ·
                refine ⟨19986235965584030841796181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13324157310389353894530787 19986235965584030841796181)
                ·
                  refine ⟨234213702721687861427299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19986235965584030841796181 234213702721687861427299)
                  ·
                    rfl

theorem cell23_4105166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_4105166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105166 prefixEnd_4105166 := by exact prefixLift 4105166
  have htrace : WordTrace (prefixWord ++ tailWord_4105166) baseStart_4105166 baseEnd_4105166 := by
    simpa [prefixWord, tailWord_4105166, baseEnd_4105166] using wordTrace_append hprefix tailTrace_4105166
  have hstable : (prefixWord ++ tailWord_4105166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105166).length < 2 ^ (prefixWord ++ tailWord_4105166).sum := by decide
  have hdescent : baseEnd_4105166 < baseStart_4105166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105170 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_4105170 : Nat := 118140960795 + 4105170 * 2 ^ 59
def prefixEnd_4105170 : Nat := 4983230072969 + 3 ^ 40 * 4105170 * 2
def baseEnd_4105170 : Nat := 702641792805936245731891

theorem tailTrace_4105170 : CollatzResearch.WordTrace tailWord_4105170 prefixEnd_4105170 702641792805936245731891 := by
  unfold tailWord_4105170
  simp only [CollatzResearch.WordTrace]
  refine ⟨37431962634419418015778241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99818567025118448042075309 37431962634419418015778241)
  ·
    refine ⟨28073971975814563511833681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37431962634419418015778241 28073971975814563511833681)
    ·
      refine ⟨21055478981860922633875261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28073971975814563511833681 21055478981860922633875261)
      ·
        refine ⟨7895804618197845987703223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21055478981860922633875261 7895804618197845987703223)
        ·
          refine ⟨11843706927296768981554835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895804618197845987703223 11843706927296768981554835)
          ·
            refine ⟨17765560390945153472332253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11843706927296768981554835 17765560390945153472332253)
            ·
              refine ⟨6662085146604432552124595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17765560390945153472332253 6662085146604432552124595)
              ·
                refine ⟨9993127719906648828186893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662085146604432552124595 9993127719906648828186893)
                ·
                  refine ⟨3747422894964993310570085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9993127719906648828186893 3747422894964993310570085)
                  ·
                    refine ⟨702641792805936245731891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3747422894964993310570085 702641792805936245731891)
                    ·
                      rfl

theorem cell23_4105170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_4105170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105170 prefixEnd_4105170 := by exact prefixLift 4105170
  have htrace : WordTrace (prefixWord ++ tailWord_4105170) baseStart_4105170 baseEnd_4105170 := by
    simpa [prefixWord, tailWord_4105170, baseEnd_4105170] using wordTrace_append hprefix tailTrace_4105170
  have hstable : (prefixWord ++ tailWord_4105170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105170).length < 2 ^ (prefixWord ++ tailWord_4105170).sum := by decide
  have hdescent : baseEnd_4105170 < baseStart_4105170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105183 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 6]
def baseStart_4105183 : Nat := 118140960795 + 4105183 * 2 ^ 59
def prefixEnd_4105183 : Nat := 4983230072969 + 3 ^ 40 * 4105183 * 2
def baseEnd_4105183 : Nat := 234214672629590798481457

theorem tailTrace_4105183 : CollatzResearch.WordTrace tailWord_4105183 prefixEnd_4105183 234214672629590798481457 := by
  unfold tailWord_4105183
  simp only [CollatzResearch.WordTrace]
  refine ⟨149728324686630575283336203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99818883124420383522224135 149728324686630575283336203)
  ·
    refine ⟨224592487029945862925004305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149728324686630575283336203 224592487029945862925004305)
    ·
      refine ⟨168444365272459397193753229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224592487029945862925004305 168444365272459397193753229)
      ·
        refine ⟨63166636977172273947657461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168444365272459397193753229 63166636977172273947657461)
        ·
          refine ⟨5921872216609900682592887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63166636977172273947657461 5921872216609900682592887)
          ·
            refine ⟨8882808324914851023889331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921872216609900682592887 8882808324914851023889331)
            ·
              refine ⟨13324212487372276535833997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882808324914851023889331 13324212487372276535833997)
              ·
                refine ⟨4996579682764603700937749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13324212487372276535833997 4996579682764603700937749)
                ·
                  refine ⟨234214672629590798481457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4996579682764603700937749 234214672629590798481457)
                  ·
                    rfl

theorem cell23_4105183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 6].length) (baseStart_4105183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105183 prefixEnd_4105183 := by exact prefixLift 4105183
  have htrace : WordTrace (prefixWord ++ tailWord_4105183) baseStart_4105183 baseEnd_4105183 := by
    simpa [prefixWord, tailWord_4105183, baseEnd_4105183] using wordTrace_append hprefix tailTrace_4105183
  have hstable : (prefixWord ++ tailWord_4105183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105183).length < 2 ^ (prefixWord ++ tailWord_4105183).sum := by decide
  have hdescent : baseEnd_4105183 < baseStart_4105183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105227 : List Nat := [1, 1, 1, 1, 6, 3, 1, 4, 1, 1, 3]
def baseStart_4105227 : Nat := 118140960795 + 4105227 * 2 ^ 59
def prefixEnd_4105227 : Nat := 4983230072969 + 3 ^ 40 * 4105227 * 2
def baseEnd_4105227 : Nat := 2107954646815115014182911

theorem tailTrace_4105227 : CollatzResearch.WordTrace tailWord_4105227 prefixEnd_4105227 2107954646815115014182911 := by
  unfold tailWord_4105227
  simp only [CollatzResearch.WordTrace]
  refine ⟨149729929498471170797937935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99819952998980780531958623 149729929498471170797937935)
  ·
    refine ⟨224594894247706756196906903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149729929498471170797937935 224594894247706756196906903)
    ·
      refine ⟨336892341371560134295360355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224594894247706756196906903 336892341371560134295360355)
      ·
        refine ⟨505338512057340201443040533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336892341371560134295360355 505338512057340201443040533)
        ·
          refine ⟨23687742752687821942642525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 505338512057340201443040533 23687742752687821942642525)
          ·
            refine ⟨8882903532257933228490947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23687742752687821942642525 8882903532257933228490947)
            ·
              refine ⟨13324355298386899842736421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882903532257933228490947 13324355298386899842736421)
              ·
                refine ⟨2498316618447543720513079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13324355298386899842736421 2498316618447543720513079)
                ·
                  refine ⟨3747474927671315580769619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498316618447543720513079 3747474927671315580769619)
                  ·
                    refine ⟨5621212391506973371154429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3747474927671315580769619 5621212391506973371154429)
                    ·
                      refine ⟨2107954646815115014182911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5621212391506973371154429 2107954646815115014182911)
                      ·
                        rfl

theorem cell23_4105227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 1, 3].length) (baseStart_4105227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105227 prefixEnd_4105227 := by exact prefixLift 4105227
  have htrace : WordTrace (prefixWord ++ tailWord_4105227) baseStart_4105227 baseEnd_4105227 := by
    simpa [prefixWord, tailWord_4105227, baseEnd_4105227] using wordTrace_append hprefix tailTrace_4105227
  have hstable : (prefixWord ++ tailWord_4105227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105227).length < 2 ^ (prefixWord ++ tailWord_4105227).sum := by decide
  have hdescent : baseEnd_4105227 < baseStart_4105227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105253 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_4105253 : Nat := 118140960795 + 4105253 * 2 ^ 59
def prefixEnd_4105253 : Nat := 4983230072969 + 3 ^ 40 * 4105253 * 2
def baseEnd_4105253 : Nat := 2107967997312131912457791

theorem tailTrace_4105253 : CollatzResearch.WordTrace tailWord_4105253 prefixEnd_4105253 2107967997312131912457791 := by
  unfold tailWord_4105253
  simp only [CollatzResearch.WordTrace]
  refine ⟨149730877796376977238384413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99820585197584651492256275 149730877796376977238384413)
  ·
    refine ⟨56149079173641366464394155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149730877796376977238384413 56149079173641366464394155)
    ·
      refine ⟨84223618760462049696591233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56149079173641366464394155 84223618760462049696591233)
      ·
        refine ⟨63167714070346537272443425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84223618760462049696591233 63167714070346537272443425)
        ·
          refine ⟨47375785552759902954332569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63167714070346537272443425 47375785552759902954332569)
          ·
            refine ⟨35531839164569927215749427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47375785552759902954332569 35531839164569927215749427)
            ·
              refine ⟨53297758746854890823624141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35531839164569927215749427 53297758746854890823624141)
              ·
                refine ⟨19986659530070584058859053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53297758746854890823624141 19986659530070584058859053)
                ·
                  refine ⟨7494997323776469022072145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19986659530070584058859053 7494997323776469022072145)
                  ·
                    refine ⟨5621247992832351766554109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7494997323776469022072145 5621247992832351766554109)
                    ·
                      refine ⟨2107967997312131912457791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5621247992832351766554109 2107967997312131912457791)
                      ·
                        rfl

theorem cell23_4105253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_4105253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105253 prefixEnd_4105253 := by exact prefixLift 4105253
  have htrace : WordTrace (prefixWord ++ tailWord_4105253) baseStart_4105253 baseEnd_4105253 := by
    simpa [prefixWord, tailWord_4105253, baseEnd_4105253] using wordTrace_append hprefix tailTrace_4105253
  have hstable : (prefixWord ++ tailWord_4105253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105253).length < 2 ^ (prefixWord ++ tailWord_4105253).sum := by decide
  have hdescent : baseEnd_4105253 < baseStart_4105253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105277 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_4105277 : Nat := 118140960795 + 4105277 * 2 ^ 59
def prefixEnd_4105277 : Nat := 4983230072969 + 3 ^ 40 * 4105277 * 2
def baseEnd_4105277 : Nat := 702660106949279939519227

theorem tailTrace_4105277 : CollatzResearch.WordTrace tailWord_4105277 prefixEnd_4105277 702660106949279939519227 := by
  unfold tailWord_4105277
  simp only [CollatzResearch.WordTrace]
  refine ⟨149731753148290029337258085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99821168765526686224838723 149731753148290029337258085)
  ·
    refine ⟨28074703715304380500735891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149731753148290029337258085 28074703715304380500735891)
    ·
      refine ⟨42112055572956570751103837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28074703715304380500735891 42112055572956570751103837)
      ·
        refine ⟨15792020839858714031663939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42112055572956570751103837 15792020839858714031663939)
        ·
          refine ⟨23688031259788071047495909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15792020839858714031663939 23688031259788071047495909)
          ·
            refine ⟨4441505861210263321405483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23688031259788071047495909 4441505861210263321405483)
            ·
              refine ⟨6662258791815394982108225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441505861210263321405483 6662258791815394982108225)
              ·
                refine ⟨4996694093861546236581169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6662258791815394982108225 4996694093861546236581169)
                ·
                  refine ⟨3747520570396159677435877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4996694093861546236581169 3747520570396159677435877)
                  ·
                    refine ⟨702660106949279939519227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3747520570396159677435877 702660106949279939519227)
                    ·
                      rfl

theorem cell23_4105277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_4105277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105277 prefixEnd_4105277 := by exact prefixLift 4105277
  have htrace : WordTrace (prefixWord ++ tailWord_4105277) baseStart_4105277 baseEnd_4105277 := by
    simpa [prefixWord, tailWord_4105277, baseEnd_4105277] using wordTrace_append hprefix tailTrace_4105277
  have hstable : (prefixWord ++ tailWord_4105277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105277).length < 2 ^ (prefixWord ++ tailWord_4105277).sum := by decide
  have hdescent : baseEnd_4105277 < baseStart_4105277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105296 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_4105296 : Nat := 118140960795 + 4105296 * 2 ^ 59
def prefixEnd_4105296 : Nat := 4983230072969 + 3 ^ 40 * 4105296 * 2
def baseEnd_4105296 : Nat := 2107990076980275244220093

theorem tailTrace_4105296 : CollatzResearch.WordTrace tailWord_4105296 prefixEnd_4105296 2107990076980275244220093 := by
  unfold tailWord_4105296
  simp only [CollatzResearch.WordTrace]
  refine ⟨74866223067610597791099871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99821630756814130388133161 74866223067610597791099871)
  ·
    refine ⟨112299334601415896686649807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74866223067610597791099871 112299334601415896686649807)
    ·
      refine ⟨168449001902123845029974711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112299334601415896686649807 168449001902123845029974711)
      ·
        refine ⟨252673502853185767544962067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168449001902123845029974711 252673502853185767544962067)
        ·
          refine ⟨379010254279778651317443101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252673502853185767544962067 379010254279778651317443101)
          ·
            refine ⟨142128845354916994244041163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379010254279778651317443101 142128845354916994244041163)
            ·
              refine ⟨213193268032375491366061745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142128845354916994244041163 213193268032375491366061745)
              ·
                refine ⟨159894951024281618524546309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213193268032375491366061745 159894951024281618524546309)
                ·
                  refine ⟨29980303317052803473352433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159894951024281618524546309 29980303317052803473352433)
                  ·
                    refine ⟨22485227487789602605014325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29980303317052803473352433 22485227487789602605014325)
                    ·
                      refine ⟨2107990076980275244220093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22485227487789602605014325 2107990076980275244220093)
                      ·
                        rfl

theorem cell23_4105296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_4105296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105296 prefixEnd_4105296 := by exact prefixLift 4105296
  have htrace : WordTrace (prefixWord ++ tailWord_4105296) baseStart_4105296 baseEnd_4105296 := by
    simpa [prefixWord, tailWord_4105296, baseEnd_4105296] using wordTrace_append hprefix tailTrace_4105296
  have hstable : (prefixWord ++ tailWord_4105296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105296).length < 2 ^ (prefixWord ++ tailWord_4105296).sum := by decide
  have hdescent : baseEnd_4105296 < baseStart_4105296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105300 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_4105300 : Nat := 118140960795 + 4105300 * 2 ^ 59
def prefixEnd_4105300 : Nat := 4983230072969 + 3 ^ 40 * 4105300 * 2
def baseEnd_4105300 : Nat := 2107992130902893228570075

theorem tailTrace_4105300 : CollatzResearch.WordTrace tailWord_4105300 prefixEnd_4105300 2107992130902893228570075 := by
  unfold tailWord_4105300
  simp only [CollatzResearch.WordTrace]
  refine ⟨74866296013603352132672677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99821728018137802843563569 74866296013603352132672677)
  ·
    refine ⟨14037430502550628524876127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74866296013603352132672677 14037430502550628524876127)
    ·
      refine ⟨21056145753825942787314191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14037430502550628524876127 21056145753825942787314191)
      ·
        refine ⟨31584218630738914180971287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21056145753825942787314191 31584218630738914180971287)
        ·
          refine ⟨47376327946108371271456931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31584218630738914180971287 47376327946108371271456931)
          ·
            refine ⟨71064491919162556907185397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47376327946108371271456931 71064491919162556907185397)
            ·
              refine ⟨6662296117421489710048631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71064491919162556907185397 6662296117421489710048631)
              ·
                refine ⟨9993444176132234565072947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662296117421489710048631 9993444176132234565072947)
                ·
                  refine ⟨14990166264198351847609421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9993444176132234565072947 14990166264198351847609421)
                  ·
                    refine ⟨5621312349074381942853533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14990166264198351847609421 5621312349074381942853533)
                    ·
                      refine ⟨2107992130902893228570075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5621312349074381942853533 2107992130902893228570075)
                      ·
                        rfl

theorem cell23_4105300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_4105300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105300 prefixEnd_4105300 := by exact prefixLift 4105300
  have htrace : WordTrace (prefixWord ++ tailWord_4105300) baseStart_4105300 baseEnd_4105300 := by
    simpa [prefixWord, tailWord_4105300, baseEnd_4105300] using wordTrace_append hprefix tailTrace_4105300
  have hstable : (prefixWord ++ tailWord_4105300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105300).length < 2 ^ (prefixWord ++ tailWord_4105300).sum := by decide
  have hdescent : baseEnd_4105300 < baseStart_4105300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105306 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_4105306 : Nat := 118140960795 + 4105306 * 2 ^ 59
def prefixEnd_4105306 : Nat := 4983230072969 + 3 ^ 40 * 4105306 * 2
def baseEnd_4105306 : Nat := 2107995211786820205095047

theorem tailTrace_4105306 : CollatzResearch.WordTrace tailWord_4105306 prefixEnd_4105306 2107995211786820205095047 := by
  unfold tailWord_4105306
  simp only [CollatzResearch.WordTrace]
  refine ⟨37433202716296241822515943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99821873910123311526709181 37433202716296241822515943)
  ·
    refine ⟨56149804074444362733773915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37433202716296241822515943 56149804074444362733773915)
    ·
      refine ⟨84224706111666544100660873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56149804074444362733773915 84224706111666544100660873)
      ·
        refine ⟨63168529583749908075495655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84224706111666544100660873 63168529583749908075495655)
        ·
          refine ⟨94752794375624862113243483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63168529583749908075495655 94752794375624862113243483)
          ·
            refine ⟨142129191563437293169865225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94752794375624862113243483 142129191563437293169865225)
            ·
              refine ⟨106596893672577969877398919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142129191563437293169865225 106596893672577969877398919)
              ·
                refine ⟨159895340508866954816098379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106596893672577969877398919 159895340508866954816098379)
                ·
                  refine ⟨239843010763300432224147569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159895340508866954816098379 239843010763300432224147569)
                  ·
                    refine ⟨179882258072475324168110677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239843010763300432224147569 179882258072475324168110677)
                    ·
                      refine ⟨2107995211786820205095047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 179882258072475324168110677 2107995211786820205095047)
                      ·
                        rfl

theorem cell23_4105306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_4105306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105306 prefixEnd_4105306 := by exact prefixLift 4105306
  have htrace : WordTrace (prefixWord ++ tailWord_4105306) baseStart_4105306 baseEnd_4105306 := by
    simpa [prefixWord, tailWord_4105306, baseEnd_4105306] using wordTrace_append hprefix tailTrace_4105306
  have hstable : (prefixWord ++ tailWord_4105306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105306).length < 2 ^ (prefixWord ++ tailWord_4105306).sum := by decide
  have hdescent : baseEnd_4105306 < baseStart_4105306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105374 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_4105374 : Nat := 118140960795 + 4105374 * 2 ^ 59
def prefixEnd_4105374 : Nat := 4983230072969 + 3 ^ 40 * 4105374 * 2
def baseEnd_4105374 : Nat := 2108030128471325939044735

theorem tailTrace_4105374 : CollatzResearch.WordTrace tailWord_4105374 prefixEnd_4105374 2108030128471325939044735 := by
  unfold tailWord_4105374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18716911378617326862942397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99823527352625743269026117 18716911378617326862942397)
  ·
    refine ⟨7018841766981497573603399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18716911378617326862942397 7018841766981497573603399)
    ·
      refine ⟨10528262650472246360405099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7018841766981497573603399 10528262650472246360405099)
      ·
        refine ⟨15792393975708369540607649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10528262650472246360405099 15792393975708369540607649)
        ·
          refine ⟨11844295481781277155455737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15792393975708369540607649 11844295481781277155455737)
          ·
            refine ⟨8883221611335957866591803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11844295481781277155455737 8883221611335957866591803)
            ·
              refine ⟨13324832417003936799887705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883221611335957866591803 13324832417003936799887705)
              ·
                refine ⟨9993624312752952599915779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13324832417003936799887705 9993624312752952599915779)
                ·
                  refine ⟨14990436469129428899873669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9993624312752952599915779 14990436469129428899873669)
                  ·
                    refine ⟨2810706837961767918726313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14990436469129428899873669 2810706837961767918726313)
                    ·
                      refine ⟨2108030128471325939044735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810706837961767918726313 2108030128471325939044735)
                      ·
                        rfl

theorem cell23_4105374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_4105374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105374 prefixEnd_4105374 := by exact prefixLift 4105374
  have htrace : WordTrace (prefixWord ++ tailWord_4105374) baseStart_4105374 baseEnd_4105374 := by
    simpa [prefixWord, tailWord_4105374, baseEnd_4105374] using wordTrace_append hprefix tailTrace_4105374
  have hstable : (prefixWord ++ tailWord_4105374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105374).length < 2 ^ (prefixWord ++ tailWord_4105374).sum := by decide
  have hdescent : baseEnd_4105374 < baseStart_4105374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105413 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_4105413 : Nat := 118140960795 + 4105413 * 2 ^ 59
def prefixEnd_4105413 : Nat := 4983230072969 + 3 ^ 40 * 4105413 * 2
def baseEnd_4105413 : Nat := 2108050154216851286457055

theorem tailTrace_4105413 : CollatzResearch.WordTrace tailWord_4105413 prefixEnd_4105413 2108050154216851286457055 := by
  unfold tailWord_4105413
  simp only [CollatzResearch.WordTrace]
  refine ⟨149736713475797324564208893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99824475650531549709472595 149736713475797324564208893)
  ·
    refine ⟨56151267553423996711578335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149736713475797324564208893 56151267553423996711578335)
    ·
      refine ⟨84226901330135995067367503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56151267553423996711578335 84226901330135995067367503)
      ·
        refine ⟨126340351995203992601051255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84226901330135995067367503 126340351995203992601051255)
        ·
          refine ⟨189510527992805988901576883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126340351995203992601051255 189510527992805988901576883)
          ·
            refine ⟨284265791989208983352365325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189510527992805988901576883 284265791989208983352365325)
            ·
              refine ⟨106599671995953368757136997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284265791989208983352365325 106599671995953368757136997)
              ·
                refine ⟨19987438499241256641963187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106599671995953368757136997 19987438499241256641963187)
                ·
                  refine ⟨29981157748861884962944781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19987438499241256641963187 29981157748861884962944781)
                  ·
                    refine ⟨11242934155823206861104293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29981157748861884962944781 11242934155823206861104293)
                    ·
                      refine ⟨2108050154216851286457055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11242934155823206861104293 2108050154216851286457055)
                      ·
                        rfl

theorem cell23_4105413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_4105413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105413 prefixEnd_4105413 := by exact prefixLift 4105413
  have htrace : WordTrace (prefixWord ++ tailWord_4105413) baseStart_4105413 baseEnd_4105413 := by
    simpa [prefixWord, tailWord_4105413, baseEnd_4105413] using wordTrace_append hprefix tailTrace_4105413
  have hstable : (prefixWord ++ tailWord_4105413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105413).length < 2 ^ (prefixWord ++ tailWord_4105413).sum := by decide
  have hdescent : baseEnd_4105413 < baseStart_4105413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105507 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 4, 3, 2]
def baseStart_4105507 : Nat := 118140960795 + 4105507 * 2 ^ 59
def prefixEnd_4105507 : Nat := 4983230072969 + 3 ^ 40 * 4105507 * 2
def baseEnd_4105507 : Nat := 2108098421398373918681623

theorem tailTrace_4105507 : CollatzResearch.WordTrace tailWord_4105507 prefixEnd_4105507 2108098421398373918681623 := by
  unfold tailWord_4105507
  simp only [CollatzResearch.WordTrace]
  refine ⟨149740141937456778618130775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99826761291637852412087183 149740141937456778618130775)
  ·
    refine ⟨224610212906185167927196163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149740141937456778618130775 224610212906185167927196163)
    ·
      refine ⟨336915319359277751890794245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224610212906185167927196163 336915319359277751890794245)
      ·
        refine ⟨63171622379864578479523921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336915319359277751890794245 63171622379864578479523921)
        ·
          refine ⟨47378716784898433859642941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63171622379864578479523921 47378716784898433859642941)
          ·
            refine ⟨17767018794336912697366103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47378716784898433859642941 17767018794336912697366103)
            ·
              refine ⟨26650528191505369046049155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17767018794336912697366103 26650528191505369046049155)
              ·
                refine ⟨39975792287258053569073733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26650528191505369046049155 39975792287258053569073733)
                ·
                  refine ⟨7495461053860885044201325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39975792287258053569073733 7495461053860885044201325)
                  ·
                    refine ⟨2810797895197831891575497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7495461053860885044201325 2810797895197831891575497)
                    ·
                      refine ⟨2108098421398373918681623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810797895197831891575497 2108098421398373918681623)
                      ·
                        rfl

theorem cell23_4105507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_4105507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105507 prefixEnd_4105507 := by exact prefixLift 4105507
  have htrace : WordTrace (prefixWord ++ tailWord_4105507) baseStart_4105507 baseEnd_4105507 := by
    simpa [prefixWord, tailWord_4105507, baseEnd_4105507] using wordTrace_append hprefix tailTrace_4105507
  have hstable : (prefixWord ++ tailWord_4105507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105507).length < 2 ^ (prefixWord ++ tailWord_4105507).sum := by decide
  have hdescent : baseEnd_4105507 < baseStart_4105507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105520 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_4105520 : Nat := 118140960795 + 4105520 * 2 ^ 59
def prefixEnd_4105520 : Nat := 4983230072969 + 3 ^ 40 * 4105520 * 2
def baseEnd_4105520 : Nat := 2108105096646882367819063

theorem tailTrace_4105520 : CollatzResearch.WordTrace tailWord_4105520 prefixEnd_4105520 2108105096646882367819063 := by
  unfold tailWord_4105520
  simp only [CollatzResearch.WordTrace]
  refine ⟨74870308043204840919177007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99827077390939787892236009 74870308043204840919177007)
  ·
    refine ⟨112305462064807261378765511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74870308043204840919177007 112305462064807261378765511)
    ·
      refine ⟨168458193097210892068148267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112305462064807261378765511 168458193097210892068148267)
      ·
        refine ⟨252687289645816338102222401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168458193097210892068148267 252687289645816338102222401)
        ·
          refine ⟨189515467234362253576666801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252687289645816338102222401 189515467234362253576666801)
          ·
            refine ⟨142136600425771690182500101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189515467234362253576666801 142136600425771690182500101)
            ·
              refine ⟨26650612579832191909218769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142136600425771690182500101 26650612579832191909218769)
              ·
                refine ⟨19987959434874143931914077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26650612579832191909218769 19987959434874143931914077)
                ·
                  refine ⟨7495484788077803974467779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19987959434874143931914077 7495484788077803974467779)
                  ·
                    refine ⟨11243227182116705961701669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7495484788077803974467779 11243227182116705961701669)
                    ·
                      refine ⟨2108105096646882367819063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11243227182116705961701669 2108105096646882367819063)
                      ·
                        rfl

theorem cell23_4105520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_4105520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105520 prefixEnd_4105520 := by exact prefixLift 4105520
  have htrace : WordTrace (prefixWord ++ tailWord_4105520) baseStart_4105520 baseEnd_4105520 := by
    simpa [prefixWord, tailWord_4105520, baseEnd_4105520] using wordTrace_append hprefix tailTrace_4105520
  have hstable : (prefixWord ++ tailWord_4105520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105520).length < 2 ^ (prefixWord ++ tailWord_4105520).sum := by decide
  have hdescent : baseEnd_4105520 < baseStart_4105520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105524 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_4105524 : Nat := 118140960795 + 4105524 * 2 ^ 59
def prefixEnd_4105524 : Nat := 4983230072969 + 3 ^ 40 * 4105524 * 2
def baseEnd_4105524 : Nat := 2108107150569500352169045

theorem tailTrace_4105524 : CollatzResearch.WordTrace tailWord_4105524 prefixEnd_4105524 2108107150569500352169045 := by
  unfold tailWord_4105524
  simp only [CollatzResearch.WordTrace]
  refine ⟨74870380989197595260749813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99827174652263460347666417 74870380989197595260749813)
  ·
    refine ⟨7019098217737274555695295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74870380989197595260749813 7019098217737274555695295)
    ·
      refine ⟨10528647326605911833542943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7019098217737274555695295 10528647326605911833542943)
      ·
        refine ⟨15792970989908867750314415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10528647326605911833542943 15792970989908867750314415)
        ·
          refine ⟨23689456484863301625471623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15792970989908867750314415 23689456484863301625471623)
          ·
            refine ⟨35534184727294952438207435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23689456484863301625471623 35534184727294952438207435)
            ·
              refine ⟨53301277090942428657311153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35534184727294952438207435 53301277090942428657311153)
              ·
                refine ⟨39975957818206821492983365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53301277090942428657311153 39975957818206821492983365)
                ·
                  refine ⟨7495492090913779029934381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39975957818206821492983365 7495492090913779029934381)
                  ·
                    refine ⟨2810809534092667136225393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7495492090913779029934381 2810809534092667136225393)
                    ·
                      refine ⟨2108107150569500352169045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810809534092667136225393 2108107150569500352169045)
                      ·
                        rfl

theorem cell23_4105524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_4105524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105524 prefixEnd_4105524 := by exact prefixLift 4105524
  have htrace : WordTrace (prefixWord ++ tailWord_4105524) baseStart_4105524 baseEnd_4105524 := by
    simpa [prefixWord, tailWord_4105524, baseEnd_4105524] using wordTrace_append hprefix tailTrace_4105524
  have hstable : (prefixWord ++ tailWord_4105524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105524).length < 2 ^ (prefixWord ++ tailWord_4105524).sum := by decide
  have hdescent : baseEnd_4105524 < baseStart_4105524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105530 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_4105530 : Nat := 118140960795 + 4105530 * 2 ^ 59
def prefixEnd_4105530 : Nat := 4983230072969 + 3 ^ 40 * 4105530 * 2
def baseEnd_4105530 : Nat := 702703410484475776231339

theorem tailTrace_4105530 : CollatzResearch.WordTrace tailWord_4105530 prefixEnd_4105530 702703410484475776231339 := by
  unfold tailWord_4105530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37435245204093363386554511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99827320544248969030812029 37435245204093363386554511)
  ·
    refine ⟨56152867806140045079831767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37435245204093363386554511 56152867806140045079831767)
    ·
      refine ⟨84229301709210067619747651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56152867806140045079831767 84229301709210067619747651)
      ·
        refine ⟨126343952563815101429621477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84229301709210067619747651 126343952563815101429621477)
        ·
          refine ⟨23689491105715331518054027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126343952563815101429621477 23689491105715331518054027)
          ·
            refine ⟨35534236658572997277081041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23689491105715331518054027 35534236658572997277081041)
            ·
              refine ⟨26650677493929747957810781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35534236658572997277081041 26650677493929747957810781)
              ·
                refine ⟨9994004060223655484179043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26650677493929747957810781 9994004060223655484179043)
                ·
                  refine ⟨14991006090335483226268565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9994004060223655484179043 14991006090335483226268565)
                  ·
                    refine ⟨702703410484475776231339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14991006090335483226268565 702703410484475776231339)
                    ·
                      rfl

theorem cell23_4105530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_4105530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105530 prefixEnd_4105530 := by exact prefixLift 4105530
  have htrace : WordTrace (prefixWord ++ tailWord_4105530) baseStart_4105530 baseEnd_4105530 := by
    simpa [prefixWord, tailWord_4105530, baseEnd_4105530] using wordTrace_append hprefix tailTrace_4105530
  have hstable : (prefixWord ++ tailWord_4105530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105530).length < 2 ^ (prefixWord ++ tailWord_4105530).sum := by decide
  have hdescent : baseEnd_4105530 < baseStart_4105530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105557 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_4105557 : Nat := 118140960795 + 4105557 * 2 ^ 59
def prefixEnd_4105557 : Nat := 4983230072969 + 3 ^ 40 * 4105557 * 2
def baseEnd_4105557 : Nat := 2108124095431098723056393

theorem tailTrace_4105557 : CollatzResearch.WordTrace tailWord_4105557 prefixEnd_4105557 2108124095431098723056393 := by
  unfold tailWord_4105557
  simp only [CollatzResearch.WordTrace]
  refine ⟨149741965587275637157450925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99827977058183758104967283 149741965587275637157450925)
  ·
    refine ⟨56153237095228363934044097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149741965587275637157450925 56153237095228363934044097)
    ·
      refine ⟨42114927821421272950533073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56153237095228363934044097 42114927821421272950533073)
      ·
        refine ⟨31586195866065954712899805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42114927821421272950533073 31586195866065954712899805)
        ·
          refine ⟨11844823449774733017337427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31586195866065954712899805 11844823449774733017337427)
          ·
            refine ⟨17767235174662099526006141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11844823449774733017337427 17767235174662099526006141)
            ·
              refine ⟨6662713190498287322252303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17767235174662099526006141 6662713190498287322252303)
              ·
                refine ⟨9994069785747430983378455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662713190498287322252303 9994069785747430983378455)
                ·
                  refine ⟨14991104678621146475067683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9994069785747430983378455 14991104678621146475067683)
                  ·
                    refine ⟨22486657017931719712601525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14991104678621146475067683 22486657017931719712601525)
                    ·
                      refine ⟨2108124095431098723056393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22486657017931719712601525 2108124095431098723056393)
                      ·
                        rfl

theorem cell23_4105557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_4105557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105557 prefixEnd_4105557 := by exact prefixLift 4105557
  have htrace : WordTrace (prefixWord ++ tailWord_4105557) baseStart_4105557 baseEnd_4105557 := by
    simpa [prefixWord, tailWord_4105557, baseEnd_4105557] using wordTrace_append hprefix tailTrace_4105557
  have hstable : (prefixWord ++ tailWord_4105557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105557).length < 2 ^ (prefixWord ++ tailWord_4105557).sum := by decide
  have hdescent : baseEnd_4105557 < baseStart_4105557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105644 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 1, 4, 2]
def baseStart_4105644 : Nat := 118140960795 + 4105644 * 2 ^ 59
def prefixEnd_4105644 : Nat := 4983230072969 + 3 ^ 40 * 4105644 * 2
def baseEnd_4105644 : Nat := 2108168768248039882668493

theorem tailTrace_4105644 : CollatzResearch.WordTrace tailWord_4105644 prefixEnd_4105644 2108168768248039882668493 := by
  unfold tailWord_4105644
  simp only [CollatzResearch.WordTrace]
  refine ⟨74872569368980225507933993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99830092491973634010578657 74872569368980225507933993)
  ·
    refine ⟨56154427026735169130950495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74872569368980225507933993 56154427026735169130950495)
    ·
      refine ⟨84231640540102753696425743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56154427026735169130950495 84231640540102753696425743)
      ·
        refine ⟨126347460810154130544638615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84231640540102753696425743 126347460810154130544638615)
        ·
          refine ⟨189521191215231195816957923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126347460810154130544638615 189521191215231195816957923)
          ·
            refine ⟨284281786822846793725436885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189521191215231195816957923 284281786822846793725436885)
            ·
              refine ⟨6662854378660471727939927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 284281786822846793725436885 6662854378660471727939927)
              ·
                refine ⟨9994281567990707591909891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662854378660471727939927 9994281567990707591909891)
                ·
                  refine ⟨14991422351986061387864837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9994281567990707591909891 14991422351986061387864837)
                  ·
                    refine ⟨2810891690997386510224657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14991422351986061387864837 2810891690997386510224657)
                    ·
                      refine ⟨2108168768248039882668493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2810891690997386510224657 2108168768248039882668493)
                      ·
                        rfl

theorem cell23_4105644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_4105644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105644 prefixEnd_4105644 := by exact prefixLift 4105644
  have htrace : WordTrace (prefixWord ++ tailWord_4105644) baseStart_4105644 baseEnd_4105644 := by
    simpa [prefixWord, tailWord_4105644, baseEnd_4105644] using wordTrace_append hprefix tailTrace_4105644
  have hstable : (prefixWord ++ tailWord_4105644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105644).length < 2 ^ (prefixWord ++ tailWord_4105644).sum := by decide
  have hdescent : baseEnd_4105644 < baseStart_4105644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105650 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 9]
def baseStart_4105650 : Nat := 118140960795 + 4105650 * 2 ^ 59
def prefixEnd_4105650 : Nat := 4983230072969 + 3 ^ 40 * 4105650 * 2
def baseEnd_4105650 : Nat := 234241316570218539910385

theorem tailTrace_4105650 : CollatzResearch.WordTrace tailWord_4105650 prefixEnd_4105650 234241316570218539910385 := by
  unfold tailWord_4105650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37436339393984678510146601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99830238383959142693724269 37436339393984678510146601)
  ·
    refine ⟨28077254545488508882609951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37436339393984678510146601 28077254545488508882609951)
    ·
      refine ⟨42115881818232763323914927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28077254545488508882609951 42115881818232763323914927)
      ·
        refine ⟨63173822727349144985872391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42115881818232763323914927 63173822727349144985872391)
        ·
          refine ⟨94760734091023717478808587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63173822727349144985872391 94760734091023717478808587)
          ·
            refine ⟨142141101136535576218212881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94760734091023717478808587 142141101136535576218212881)
            ·
              refine ⟨106605825852401682163659661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142141101136535576218212881 106605825852401682163659661)
              ·
                refine ⟨39977184694650630811372373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106605825852401682163659661 39977184694650630811372373)
                ·
                  refine ⟨234241316570218539910385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39977184694650630811372373 234241316570218539910385)
                  ·
                    rfl

theorem cell23_4105650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_4105650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105650 prefixEnd_4105650 := by exact prefixLift 4105650
  have htrace : WordTrace (prefixWord ++ tailWord_4105650) baseStart_4105650 baseEnd_4105650 := by
    simpa [prefixWord, tailWord_4105650, baseEnd_4105650] using wordTrace_append hprefix tailTrace_4105650
  have hstable : (prefixWord ++ tailWord_4105650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105650).length < 2 ^ (prefixWord ++ tailWord_4105650).sum := by decide
  have hdescent : baseEnd_4105650 < baseStart_4105650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105714 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_4105714 : Nat := 118140960795 + 4105714 * 2 ^ 59
def prefixEnd_4105714 : Nat := 4983230072969 + 3 ^ 40 * 4105714 * 2
def baseEnd_4105714 : Nat := 702734903964618202931057

theorem tailTrace_4105714 : CollatzResearch.WordTrace tailWord_4105714 prefixEnd_4105714 702734903964618202931057 := by
  unfold tailWord_4105714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37436922961926713242729049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99831794565137901980610797 37436922961926713242729049)
  ·
    refine ⟨28077692221445034932046787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37436922961926713242729049 28077692221445034932046787)
    ·
      refine ⟨42116538332167552398070181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28077692221445034932046787 42116538332167552398070181)
      ·
        refine ⟨7896850937281416074638159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42116538332167552398070181 7896850937281416074638159)
        ·
          refine ⟨11845276405922124111957239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7896850937281416074638159 11845276405922124111957239)
          ·
            refine ⟨17767914608883186167935859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11845276405922124111957239 17767914608883186167935859)
            ·
              refine ⟨26651871913324779251903789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17767914608883186167935859 26651871913324779251903789)
              ·
                refine ⟨9994451967496792219463921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26651871913324779251903789 9994451967496792219463921)
                ·
                  refine ⟨7495838975622594164597941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9994451967496792219463921 7495838975622594164597941)
                  ·
                    refine ⟨702734903964618202931057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7495838975622594164597941 702734903964618202931057)
                    ·
                      rfl

theorem cell23_4105714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_4105714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105714 prefixEnd_4105714 := by exact prefixLift 4105714
  have htrace : WordTrace (prefixWord ++ tailWord_4105714) baseStart_4105714 baseEnd_4105714 := by
    simpa [prefixWord, tailWord_4105714, baseEnd_4105714] using wordTrace_append hprefix tailTrace_4105714
  have hstable : (prefixWord ++ tailWord_4105714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105714).length < 2 ^ (prefixWord ++ tailWord_4105714).sum := by decide
  have hdescent : baseEnd_4105714 < baseStart_4105714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105727 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 7, 4]
def baseStart_4105727 : Nat := 118140960795 + 4105727 * 2 ^ 59
def prefixEnd_4105727 : Nat := 4983230072969 + 3 ^ 40 * 4105727 * 2
def baseEnd_4105727 : Nat := 702737129047454352643537

theorem tailTrace_4105727 : CollatzResearch.WordTrace tailWord_4105727 prefixEnd_4105727 702737129047454352643537 := by
  unfold tailWord_4105727
  simp only [CollatzResearch.WordTrace]
  refine ⟨149748165996659756191139435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99832110664439837460759623 149748165996659756191139435)
  ·
    refine ⟨224622248994989634286709153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149748165996659756191139435 224622248994989634286709153)
    ·
      refine ⟨168466686746242225715031865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224622248994989634286709153 168466686746242225715031865)
      ·
        refine ⟨126350015059681669286273899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168466686746242225715031865 126350015059681669286273899)
        ·
          refine ⟨189525022589522503929410849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126350015059681669286273899 189525022589522503929410849)
          ·
            refine ⟨142143766942141877947058137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189525022589522503929410849 142143766942141877947058137)
            ·
              refine ⟨106607825206606408460293603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142143766942141877947058137 106607825206606408460293603)
              ·
                refine ⟨159911737809909612690440405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106607825206606408460293603 159911737809909612690440405)
                ·
                  refine ⟨3747931354919756547432197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 159911737809909612690440405 3747931354919756547432197)
                  ·
                    refine ⟨702737129047454352643537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3747931354919756547432197 702737129047454352643537)
                    ·
                      rfl

theorem cell23_4105727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 4].length) (baseStart_4105727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105727 prefixEnd_4105727 := by exact prefixLift 4105727
  have htrace : WordTrace (prefixWord ++ tailWord_4105727) baseStart_4105727 baseEnd_4105727 := by
    simpa [prefixWord, tailWord_4105727, baseEnd_4105727] using wordTrace_append hprefix tailTrace_4105727
  have hstable : (prefixWord ++ tailWord_4105727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105727).length < 2 ^ (prefixWord ++ tailWord_4105727).sum := by decide
  have hdescent : baseEnd_4105727 < baseStart_4105727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105768 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4105768 : Nat := 118140960795 + 4105768 * 2 ^ 59
def prefixEnd_4105768 : Nat := 4983230072969 + 3 ^ 40 * 4105768 * 2
def baseEnd_4105768 : Nat := 2108232439849197397517923

theorem tailTrace_4105768 : CollatzResearch.WordTrace tailWord_4105768 prefixEnd_4105768 2108232439849197397517923 := by
  unfold tailWord_4105768
  simp only [CollatzResearch.WordTrace]
  refine ⟨74874830694755610096690979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99833107593007480128921305 74874830694755610096690979)
  ·
    refine ⟨112312246042133415145036469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74874830694755610096690979 112312246042133415145036469)
    ·
      refine ⟨10529273066450007669847169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112312246042133415145036469 10529273066450007669847169)
      ·
        refine ⟨7896954799837505752385377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10529273066450007669847169 7896954799837505752385377)
        ·
          refine ⟨5922716099878129314289033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7896954799837505752385377 5922716099878129314289033)
          ·
            refine ⟨4442037074908596985716775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5922716099878129314289033 4442037074908596985716775)
            ·
              refine ⟨6663055612362895478575163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442037074908596985716775 6663055612362895478575163)
              ·
                refine ⟨9994583418544343217862745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663055612362895478575163 9994583418544343217862745)
                ·
                  refine ⟨7495937563908257413397059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9994583418544343217862745 7495937563908257413397059)
                  ·
                    refine ⟨11243906345862386120095589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7495937563908257413397059 11243906345862386120095589)
                    ·
                      refine ⟨2108232439849197397517923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11243906345862386120095589 2108232439849197397517923)
                      ·
                        rfl

theorem cell23_4105768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4105768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105768 prefixEnd_4105768 := by exact prefixLift 4105768
  have htrace : WordTrace (prefixWord ++ tailWord_4105768) baseStart_4105768 baseEnd_4105768 := by
    simpa [prefixWord, tailWord_4105768, baseEnd_4105768] using wordTrace_append hprefix tailTrace_4105768
  have hstable : (prefixWord ++ tailWord_4105768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105768).length < 2 ^ (prefixWord ++ tailWord_4105768).sum := by decide
  have hdescent : baseEnd_4105768 < baseStart_4105768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105824 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 1, 8, 2]
def baseStart_4105824 : Nat := 118140960795 + 4105824 * 2 ^ 59
def prefixEnd_4105824 : Nat := 4983230072969 + 3 ^ 40 * 4105824 * 2
def baseEnd_4105824 : Nat := 2108261194765849178417665

theorem tailTrace_4105824 : CollatzResearch.WordTrace tailWord_4105824 prefixEnd_4105824 2108261194765849178417665 := by
  unfold tailWord_4105824
  simp only [CollatzResearch.WordTrace]
  refine ⟨74875851938654170878710263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99834469251538894504947017 74875851938654170878710263)
  ·
    refine ⟨112313777907981256318065395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74875851938654170878710263 112313777907981256318065395)
    ·
      refine ⟨168470666861971884477098093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112313777907981256318065395 168470666861971884477098093)
      ·
        refine ⟨63176500073239456678911785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168470666861971884477098093 63176500073239456678911785)
        ·
          refine ⟨47382375054929592509183839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63176500073239456678911785 47382375054929592509183839)
          ·
            refine ⟨71073562582394388763775759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47382375054929592509183839 71073562582394388763775759)
            ·
              refine ⟨106610343873591583145663639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71073562582394388763775759 106610343873591583145663639)
              ·
                refine ⟨159915515810387374718495459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106610343873591583145663639 159915515810387374718495459)
                ·
                  refine ⟨239873273715581062077743189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159915515810387374718495459 239873273715581062077743189)
                  ·
                    refine ⟨2811014926354465571223553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 239873273715581062077743189 2811014926354465571223553)
                    ·
                      refine ⟨2108261194765849178417665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811014926354465571223553 2108261194765849178417665)
                      ·
                        rfl

theorem cell23_4105824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_4105824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105824 prefixEnd_4105824 := by exact prefixLift 4105824
  have htrace : WordTrace (prefixWord ++ tailWord_4105824) baseStart_4105824 baseEnd_4105824 := by
    simpa [prefixWord, tailWord_4105824, baseEnd_4105824] using wordTrace_append hprefix tailTrace_4105824
  have hstable : (prefixWord ++ tailWord_4105824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105824).length < 2 ^ (prefixWord ++ tailWord_4105824).sum := by decide
  have hdescent : baseEnd_4105824 < baseStart_4105824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105841 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 5, 2, 2]
def baseStart_4105841 : Nat := 118140960795 + 4105841 * 2 ^ 59
def prefixEnd_4105841 : Nat := 4983230072969 + 3 ^ 40 * 4105841 * 2
def baseEnd_4105841 : Nat := 2108269923936975611905087

theorem tailTrace_4105841 : CollatzResearch.WordTrace tailWord_4105841 prefixEnd_4105841 2108269923936975611905087 := by
  unfold tailWord_4105841
  simp only [CollatzResearch.WordTrace]
  refine ⟨149752323918246753660789377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99834882612164502440526251 149752323918246753660789377)
  ·
    refine ⟨112314242938685065245592033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149752323918246753660789377 112314242938685065245592033)
    ·
      refine ⟨84235682204013798934194025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112314242938685065245592033 84235682204013798934194025)
      ·
        refine ⟨63176761653010349200645519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84235682204013798934194025 63176761653010349200645519)
        ·
          refine ⟨94765142479515523800968279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63176761653010349200645519 94765142479515523800968279)
          ·
            refine ⟨142147713719273285701452419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94765142479515523800968279 142147713719273285701452419)
            ·
              refine ⟨213221570578909928552178629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142147713719273285701452419 213221570578909928552178629)
              ·
                refine ⟨39979044483545611603533493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213221570578909928552178629 39979044483545611603533493)
                ·
                  refine ⟨3748035420332401087831265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39979044483545611603533493 3748035420332401087831265)
                  ·
                    refine ⟨2811026565249300815873449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3748035420332401087831265 2811026565249300815873449)
                    ·
                      refine ⟨2108269923936975611905087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811026565249300815873449 2108269923936975611905087)
                      ·
                        rfl

theorem cell23_4105841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_4105841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105841 prefixEnd_4105841 := by exact prefixLift 4105841
  have htrace : WordTrace (prefixWord ++ tailWord_4105841) baseStart_4105841 baseEnd_4105841 := by
    simpa [prefixWord, tailWord_4105841, baseEnd_4105841] using wordTrace_append hprefix tailTrace_4105841
  have hstable : (prefixWord ++ tailWord_4105841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105841).length < 2 ^ (prefixWord ++ tailWord_4105841).sum := by decide
  have hdescent : baseEnd_4105841 < baseStart_4105841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105867 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 6]
def baseStart_4105867 : Nat := 118140960795 + 4105867 * 2 ^ 59
def prefixEnd_4105867 : Nat := 4983230072969 + 3 ^ 40 * 4105867 * 2
def baseEnd_4105867 : Nat := 2108283274433992510179967

theorem tailTrace_4105867 : CollatzResearch.WordTrace tailWord_4105867 prefixEnd_4105867 2108283274433992510179967 := by
  unfold tailWord_4105867
  simp only [CollatzResearch.WordTrace]
  refine ⟨149753272216152560101235855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99835514810768373400823903 149753272216152560101235855)
  ·
    refine ⟨224629908324228840151853783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149753272216152560101235855 224629908324228840151853783)
    ·
      refine ⟨336944862486343260227780675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224629908324228840151853783 336944862486343260227780675)
      ·
        refine ⟨505417293729514890341671013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336944862486343260227780675 505417293729514890341671013)
        ·
          refine ⟨94765742574284041939063315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505417293729514890341671013 94765742574284041939063315)
          ·
            refine ⟨142148613861426062908594973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94765742574284041939063315 142148613861426062908594973)
            ·
              refine ⟨53305730198034773590723115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142148613861426062908594973 53305730198034773590723115)
              ·
                refine ⟨79958595297052160386084673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53305730198034773590723115 79958595297052160386084673)
                ·
                  refine ⟨59968946472789120289563505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79958595297052160386084673 59968946472789120289563505)
                  ·
                    refine ⟨44976709854591840217172629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59968946472789120289563505 44976709854591840217172629)
                    ·
                      refine ⟨2108283274433992510179967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44976709854591840217172629 2108283274433992510179967)
                      ·
                        rfl

theorem cell23_4105867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_4105867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105867 prefixEnd_4105867 := by exact prefixLift 4105867
  have htrace : WordTrace (prefixWord ++ tailWord_4105867) baseStart_4105867 baseEnd_4105867 := by
    simpa [prefixWord, tailWord_4105867, baseEnd_4105867] using wordTrace_append hprefix tailTrace_4105867
  have hstable : (prefixWord ++ tailWord_4105867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105867).length < 2 ^ (prefixWord ++ tailWord_4105867).sum := by decide
  have hdescent : baseEnd_4105867 < baseStart_4105867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105914 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_4105914 : Nat := 118140960795 + 4105914 * 2 ^ 59
def prefixEnd_4105914 : Nat := 4983230072969 + 3 ^ 40 * 4105914 * 2
def baseEnd_4105914 : Nat := 2108307408024753826292251

theorem tailTrace_4105914 : CollatzResearch.WordTrace tailWord_4105914 prefixEnd_4105914 2108307408024753826292251 := by
  unfold tailWord_4105914
  simp only [CollatzResearch.WordTrace]
  refine ⟨37438746611745571782049199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99836657631321524752131197 37438746611745571782049199)
  ·
    refine ⟨56158119917618357673073799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37438746611745571782049199 56158119917618357673073799)
    ·
      refine ⟨84237179876427536509610699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56158119917618357673073799 84237179876427536509610699)
      ·
        refine ⟨126355769814641304764416049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84237179876427536509610699 126355769814641304764416049)
        ·
          refine ⟨94766827360980978573312037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126355769814641304764416049 94766827360980978573312037)
          ·
            refine ⟨17768780130183933482496007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94766827360980978573312037 17768780130183933482496007)
            ·
              refine ⟨26653170195275900223744011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17768780130183933482496007 26653170195275900223744011)
              ·
                refine ⟨39979755292913850335616017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26653170195275900223744011 39979755292913850335616017)
                ·
                  refine ⟨29984816469685387751712013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39979755292913850335616017 29984816469685387751712013)
                  ·
                    refine ⟨11244306176132020406892005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29984816469685387751712013 11244306176132020406892005)
                    ·
                      refine ⟨2108307408024753826292251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11244306176132020406892005 2108307408024753826292251)
                      ·
                        rfl

theorem cell23_4105914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_4105914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105914 prefixEnd_4105914 := by exact prefixLift 4105914
  have htrace : WordTrace (prefixWord ++ tailWord_4105914) baseStart_4105914 baseEnd_4105914 := by
    simpa [prefixWord, tailWord_4105914, baseEnd_4105914] using wordTrace_append hprefix tailTrace_4105914
  have hstable : (prefixWord ++ tailWord_4105914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105914).length < 2 ^ (prefixWord ++ tailWord_4105914).sum := by decide
  have hdescent : baseEnd_4105914 < baseStart_4105914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105918 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_4105918 : Nat := 118140960795 + 4105918 * 2 ^ 59
def prefixEnd_4105918 : Nat := 4983230072969 + 3 ^ 40 * 4105918 * 2
def baseEnd_4105918 : Nat := 2108309461947371810642233

theorem tailTrace_4105918 : CollatzResearch.WordTrace tailWord_4105918 prefixEnd_4105918 2108309461947371810642233 := by
  unfold tailWord_4105918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18719391542370974476417801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99836754892645197207561605 18719391542370974476417801)
  ·
    refine ⟨14039543656778230857313351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18719391542370974476417801 14039543656778230857313351)
    ·
      refine ⟨21059315485167346285970027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14039543656778230857313351 21059315485167346285970027)
      ·
        refine ⟨31588973227751019428955041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21059315485167346285970027 31588973227751019428955041)
        ·
          refine ⟨23691729920813264571716281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31588973227751019428955041 23691729920813264571716281)
          ·
            refine ⟨17768797440609948428787211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23691729920813264571716281 17768797440609948428787211)
            ·
              refine ⟨26653196160914922643180817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17768797440609948428787211 26653196160914922643180817)
              ·
                refine ⟨19989897120686191982385613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26653196160914922643180817 19989897120686191982385613)
                ·
                  refine ⟨7496211420257321993394605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19989897120686191982385613 7496211420257321993394605)
                  ·
                    refine ⟨2811079282596495747522977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7496211420257321993394605 2811079282596495747522977)
                    ·
                      refine ⟨2108309461947371810642233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811079282596495747522977 2108309461947371810642233)
                      ·
                        rfl

theorem cell23_4105918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_4105918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105918 prefixEnd_4105918 := by exact prefixLift 4105918
  have htrace : WordTrace (prefixWord ++ tailWord_4105918) baseStart_4105918 baseEnd_4105918 := by
    simpa [prefixWord, tailWord_4105918, baseEnd_4105918] using wordTrace_append hprefix tailTrace_4105918
  have hstable : (prefixWord ++ tailWord_4105918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105918).length < 2 ^ (prefixWord ++ tailWord_4105918).sum := by decide
  have hdescent : baseEnd_4105918 < baseStart_4105918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105922 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4105922 : Nat := 118140960795 + 4105922 * 2 ^ 59
def prefixEnd_4105922 : Nat := 4983230072969 + 3 ^ 40 * 4105922 * 2
def baseEnd_4105922 : Nat := 2108311515869989794992215

theorem tailTrace_4105922 : CollatzResearch.WordTrace tailWord_4105922 prefixEnd_4105922 2108311515869989794992215 := by
  unfold tailWord_4105922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37438819557738326123622005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99836852153968869662992013 37438819557738326123622005)
  ·
    refine ⟨3509889333537968074089563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37438819557738326123622005 3509889333537968074089563)
    ·
      refine ⟨5264834000306952111134345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3509889333537968074089563 5264834000306952111134345)
      ·
        refine ⟨3948625500230214083350759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5264834000306952111134345 3948625500230214083350759)
        ·
          refine ⟨5922938250345321125026139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3948625500230214083350759 5922938250345321125026139)
          ·
            refine ⟨8884407375517981687539209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922938250345321125026139 8884407375517981687539209)
            ·
              refine ⟨6663305531638486265654407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8884407375517981687539209 6663305531638486265654407)
              ·
                refine ⟨9994958297457729398481611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663305531638486265654407 9994958297457729398481611)
                ·
                  refine ⟨14992437446186594097722417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9994958297457729398481611 14992437446186594097722417)
                  ·
                    refine ⟨11244328084639945573291813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14992437446186594097722417 11244328084639945573291813)
                    ·
                      refine ⟨2108311515869989794992215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11244328084639945573291813 2108311515869989794992215)
                      ·
                        rfl

theorem cell23_4105922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4105922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105922 prefixEnd_4105922 := by exact prefixLift 4105922
  have htrace : WordTrace (prefixWord ++ tailWord_4105922) baseStart_4105922 baseEnd_4105922 := by
    simpa [prefixWord, tailWord_4105922, baseEnd_4105922] using wordTrace_append hprefix tailTrace_4105922
  have hstable : (prefixWord ++ tailWord_4105922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105922).length < 2 ^ (prefixWord ++ tailWord_4105922).sum := by decide
  have hdescent : baseEnd_4105922 < baseStart_4105922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105944 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_4105944 : Nat := 118140960795 + 4105944 * 2 ^ 59
def prefixEnd_4105944 : Nat := 4983230072969 + 3 ^ 40 * 4105944 * 2
def baseEnd_4105944 : Nat := 2108322812444388708917113

theorem tailTrace_4105944 : CollatzResearch.WordTrace tailWord_4105944 prefixEnd_4105944 2108322812444388708917113 := by
  unfold tailWord_4105944
  simp only [CollatzResearch.WordTrace]
  refine ⟨74878040318436801125894443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99837387091249068167859257 74878040318436801125894443)
  ·
    refine ⟨112317060477655201688841665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74878040318436801125894443 112317060477655201688841665)
    ·
      refine ⟨84237795358241401266631249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112317060477655201688841665 84237795358241401266631249)
      ·
        refine ⟨63178346518681050949973437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84237795358241401266631249 63178346518681050949973437)
        ·
          refine ⟨23691879944505394106240039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63178346518681050949973437 23691879944505394106240039)
          ·
            refine ⟨35537819916758091159360059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23691879944505394106240039 35537819916758091159360059)
            ·
              refine ⟨53306729875137136739040089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35537819916758091159360059 53306729875137136739040089)
              ·
                refine ⟨39980047406352852554280067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53306729875137136739040089 39980047406352852554280067)
                ·
                  refine ⟨59970071109529278831420101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39980047406352852554280067 59970071109529278831420101)
                  ·
                    refine ⟨11244388333036739780891269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59970071109529278831420101 11244388333036739780891269)
                    ·
                      refine ⟨2108322812444388708917113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11244388333036739780891269 2108322812444388708917113)
                      ·
                        rfl

theorem cell23_4105944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_4105944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105944 prefixEnd_4105944 := by exact prefixLift 4105944
  have htrace : WordTrace (prefixWord ++ tailWord_4105944) baseStart_4105944 baseEnd_4105944 := by
    simpa [prefixWord, tailWord_4105944, baseEnd_4105944] using wordTrace_append hprefix tailTrace_4105944
  have hstable : (prefixWord ++ tailWord_4105944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105944).length < 2 ^ (prefixWord ++ tailWord_4105944).sum := by decide
  have hdescent : baseEnd_4105944 < baseStart_4105944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105959 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4105959 : Nat := 118140960795 + 4105959 * 2 ^ 59
def prefixEnd_4105959 : Nat := 4983230072969 + 3 ^ 40 * 4105959 * 2
def baseEnd_4105959 : Nat := 2108330514654206150229545

theorem tailTrace_4105959 : CollatzResearch.WordTrace tailWord_4105959 prefixEnd_4105959 2108330514654206150229545 := by
  unfold tailWord_4105959
  simp only [CollatzResearch.WordTrace]
  refine ⟨149756627731819259813584931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99837751821212839875723287 149756627731819259813584931)
  ·
    refine ⟨224634941597728889720377397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149756627731819259813584931 224634941597728889720377397)
    ·
      refine ⟨21059525774787083411285381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224634941597728889720377397 21059525774787083411285381)
      ·
        refine ⟨3948661082772578139616009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21059525774787083411285381 3948661082772578139616009)
        ·
          refine ⟨2961495812079433604712007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3948661082772578139616009 2961495812079433604712007)
          ·
            refine ⟨4442243718119150407068011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961495812079433604712007 4442243718119150407068011)
            ·
              refine ⟨6663365577178725610602017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442243718119150407068011 6663365577178725610602017)
              ·
                refine ⟨4997524182884044207951513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6663365577178725610602017 4997524182884044207951513)
                ·
                  refine ⟨3748143137163033155963635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4997524182884044207951513 3748143137163033155963635)
                  ·
                    refine ⟨5622214705744549733945453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3748143137163033155963635 5622214705744549733945453)
                    ·
                      refine ⟨2108330514654206150229545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5622214705744549733945453 2108330514654206150229545)
                      ·
                        rfl

theorem cell23_4105959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4105959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105959 prefixEnd_4105959 := by exact prefixLift 4105959
  have htrace : WordTrace (prefixWord ++ tailWord_4105959) baseStart_4105959 baseEnd_4105959 := by
    simpa [prefixWord, tailWord_4105959, baseEnd_4105959] using wordTrace_append hprefix tailTrace_4105959
  have hstable : (prefixWord ++ tailWord_4105959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105959).length < 2 ^ (prefixWord ++ tailWord_4105959).sum := by decide
  have hdescent : baseEnd_4105959 < baseStart_4105959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105965 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_4105965 : Nat := 118140960795 + 4105965 * 2 ^ 59
def prefixEnd_4105965 : Nat := 4983230072969 + 3 ^ 40 * 4105965 * 2
def baseEnd_4105965 : Nat := 2108333595538133126754517

theorem tailTrace_4105965 : CollatzResearch.WordTrace tailWord_4105965 prefixEnd_4105965 2108333595538133126754517 := by
  unfold tailWord_4105965
  simp only [CollatzResearch.WordTrace]
  refine ⟨149756846569797522838303349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99837897713198348558868899 149756846569797522838303349)
  ·
    refine ⟨14039704365918517766090939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149756846569797522838303349 14039704365918517766090939)
    ·
      refine ⟨21059556548877776649136409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14039704365918517766090939 21059556548877776649136409)
      ·
        refine ⟨15794667411658332486852307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21059556548877776649136409 15794667411658332486852307)
        ·
          refine ⟨23692001117487498730278461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15794667411658332486852307 23692001117487498730278461)
          ·
            refine ⟨8884500419057812023854423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23692001117487498730278461 8884500419057812023854423)
            ·
              refine ⟨13326750628586718035781635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884500419057812023854423 13326750628586718035781635)
              ·
                refine ⟨19990125942880077053672453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13326750628586718035781635 19990125942880077053672453)
                ·
                  refine ⟨3748148614290014447563585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19990125942880077053672453 3748148614290014447563585)
                  ·
                    refine ⟨2811111460717510835672689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3748148614290014447563585 2811111460717510835672689)
                    ·
                      refine ⟨2108333595538133126754517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811111460717510835672689 2108333595538133126754517)
                      ·
                        rfl

theorem cell23_4105965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_4105965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105965 prefixEnd_4105965 := by exact prefixLift 4105965
  have htrace : WordTrace (prefixWord ++ tailWord_4105965) baseStart_4105965 baseEnd_4105965 := by
    simpa [prefixWord, tailWord_4105965, baseEnd_4105965] using wordTrace_append hprefix tailTrace_4105965
  have hstable : (prefixWord ++ tailWord_4105965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105965).length < 2 ^ (prefixWord ++ tailWord_4105965).sum := by decide
  have hdescent : baseEnd_4105965 < baseStart_4105965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105971 : List Nat := [1, 1, 1, 2, 2, 3, 4, 4, 5]
def baseStart_4105971 : Nat := 118140960795 + 4105971 * 2 ^ 59
def prefixEnd_4105971 : Nat := 4983230072969 + 3 ^ 40 * 4105971 * 2
def baseEnd_4105971 : Nat := 234259630713562233697721

theorem tailTrace_4105971 : CollatzResearch.WordTrace tailWord_4105971 prefixEnd_4105971 234259630713562233697721 := by
  unfold tailWord_4105971
  simp only [CollatzResearch.WordTrace]
  refine ⟨149757065407775785863021767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99838043605183857242014511 149757065407775785863021767)
  ·
    refine ⟨224635598111663678794532651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149757065407775785863021767 224635598111663678794532651)
    ·
      refine ⟨336953397167495518191798977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224635598111663678794532651 336953397167495518191798977)
      ·
        refine ⟨252715047875621638643849233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336953397167495518191798977 252715047875621638643849233)
        ·
          refine ⟨189536285906716228982886925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252715047875621638643849233 189536285906716228982886925)
          ·
            refine ⟨71076107215018585868582597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189536285906716228982886925 71076107215018585868582597)
            ·
              refine ⟨13326770102815984850359237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71076107215018585868582597 13326770102815984850359237)
              ·
                refine ⟨2498769394277997159442357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13326770102815984850359237 2498769394277997159442357)
                ·
                  refine ⟨234259630713562233697721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2498769394277997159442357 234259630713562233697721)
                  ·
                    rfl

theorem cell23_4105971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 5].length) (baseStart_4105971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105971 prefixEnd_4105971 := by exact prefixLift 4105971
  have htrace : WordTrace (prefixWord ++ tailWord_4105971) baseStart_4105971 baseEnd_4105971 := by
    simpa [prefixWord, tailWord_4105971, baseEnd_4105971] using wordTrace_append hprefix tailTrace_4105971
  have hstable : (prefixWord ++ tailWord_4105971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105971).length < 2 ^ (prefixWord ++ tailWord_4105971).sum := by decide
  have hdescent : baseEnd_4105971 < baseStart_4105971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105982 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_4105982 : Nat := 118140960795 + 4105982 * 2 ^ 59
def prefixEnd_4105982 : Nat := 4983230072969 + 3 ^ 40 * 4105982 * 2
def baseEnd_4105982 : Nat := 2108342324709259560241939

theorem tailTrace_4105982 : CollatzResearch.WordTrace tailWord_4105982 prefixEnd_4105982 2108342324709259560241939 := by
  unfold tailWord_4105982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18719683326341991842709025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99838311073823956494448133 18719683326341991842709025)
  ·
    refine ⟨14039762494756493882031769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18719683326341991842709025 14039762494756493882031769)
    ·
      refine ⟨10529821871067370411523827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14039762494756493882031769 10529821871067370411523827)
      ·
        refine ⟨15794732806601055617285741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10529821871067370411523827 15794732806601055617285741)
        ·
          refine ⟨5923024802475395856482153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15794732806601055617285741 5923024802475395856482153)
          ·
            refine ⟨4442268601856546892361615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5923024802475395856482153 4442268601856546892361615)
            ·
              refine ⟨6663402902784820338542423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442268601856546892361615 6663402902784820338542423)
              ·
                refine ⟨9995104354177230507813635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663402902784820338542423 9995104354177230507813635)
                ·
                  refine ⟨14992656531265845761720453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9995104354177230507813635 14992656531265845761720453)
                  ·
                    refine ⟨2811123099612346080322585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14992656531265845761720453 2811123099612346080322585)
                    ·
                      refine ⟨2108342324709259560241939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811123099612346080322585 2108342324709259560241939)
                      ·
                        rfl

theorem cell23_4105982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_4105982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105982 prefixEnd_4105982 := by exact prefixLift 4105982
  have htrace : WordTrace (prefixWord ++ tailWord_4105982) baseStart_4105982 baseEnd_4105982 := by
    simpa [prefixWord, tailWord_4105982, baseEnd_4105982] using wordTrace_append hprefix tailTrace_4105982
  have hstable : (prefixWord ++ tailWord_4105982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105982).length < 2 ^ (prefixWord ++ tailWord_4105982).sum := by decide
  have hdescent : baseEnd_4105982 < baseStart_4105982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105984 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 4, 5]
def baseStart_4105984 : Nat := 118140960795 + 4105984 * 2 ^ 59
def prefixEnd_4105984 : Nat := 4983230072969 + 3 ^ 40 * 4105984 * 2
def baseEnd_4105984 : Nat := 702781117223522850805643

theorem tailTrace_4105984 : CollatzResearch.WordTrace tailWord_4105984 prefixEnd_4105984 702781117223522850805643 := by
  unfold tailWord_4105984
  simp only [CollatzResearch.WordTrace]
  refine ⟨74878769778364344541622503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99838359704485792722163337 74878769778364344541622503)
  ·
    refine ⟨112318154667546516812433755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74878769778364344541622503 112318154667546516812433755)
    ·
      refine ⟨168477232001319775218650633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112318154667546516812433755 168477232001319775218650633)
      ·
        refine ⟨126357924000989831413987975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168477232001319775218650633 126357924000989831413987975)
        ·
          refine ⟨189536886001484747120981963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126357924000989831413987975 189536886001484747120981963)
          ·
            refine ⟨284305329002227120681472945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189536886001484747120981963 284305329002227120681472945)
            ·
              refine ⟨213228996751670340511104709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284305329002227120681472945 213228996751670340511104709)
              ·
                refine ⟨39980436890938188845832133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213228996751670340511104709 39980436890938188845832133)
                ·
                  refine ⟨7496331917050910408593525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39980436890938188845832133 7496331917050910408593525)
                  ·
                    refine ⟨702781117223522850805643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7496331917050910408593525 702781117223522850805643)
                    ·
                      rfl

theorem cell23_4105984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_4105984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4105984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4105984 prefixEnd_4105984 := by exact prefixLift 4105984
  have htrace : WordTrace (prefixWord ++ tailWord_4105984) baseStart_4105984 baseEnd_4105984 := by
    simpa [prefixWord, tailWord_4105984, baseEnd_4105984] using wordTrace_append hprefix tailTrace_4105984
  have hstable : (prefixWord ++ tailWord_4105984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105984).length < 2 ^ (prefixWord ++ tailWord_4105984).sum := by decide
  have hdescent : baseEnd_4105984 < baseStart_4105984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106021 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_4106021 : Nat := 118140960795 + 4106021 * 2 ^ 59
def prefixEnd_4106021 : Nat := 4983230072969 + 3 ^ 40 * 4106021 * 2
def baseEnd_4106021 : Nat := 2108362350454784907654259

theorem tailTrace_4106021 : CollatzResearch.WordTrace tailWord_4106021 prefixEnd_4106021 2108362350454784907654259 := by
  unfold tailWord_4106021
  simp only [CollatzResearch.WordTrace]
  refine ⟨149758889057594644402341917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99839259371729762934894611 149758889057594644402341917)
  ·
    refine ⟨56159583396597991650878219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149758889057594644402341917 56159583396597991650878219)
    ·
      refine ⟨84239375094896987476317329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56159583396597991650878219 84239375094896987476317329)
      ·
        refine ⟨63179531321172740607237997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84239375094896987476317329 63179531321172740607237997)
        ·
          refine ⟨23692324245439777727714249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63179531321172740607237997 23692324245439777727714249)
          ·
            refine ⟨17769243184079833295785687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23692324245439777727714249 17769243184079833295785687)
            ·
              refine ⟨26653864776119749943678531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17769243184079833295785687 26653864776119749943678531)
              ·
                refine ⟨39980797164179624915517797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26653864776119749943678531 39980797164179624915517797)
                ·
                  refine ⟨7496399468283679671659587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39980797164179624915517797 7496399468283679671659587)
                  ·
                    refine ⟨11244599202425519507489381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7496399468283679671659587 11244599202425519507489381)
                    ·
                      refine ⟨2108362350454784907654259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11244599202425519507489381 2108362350454784907654259)
                      ·
                        rfl

theorem cell23_4106021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_4106021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106021 prefixEnd_4106021 := by exact prefixLift 4106021
  have htrace : WordTrace (prefixWord ++ tailWord_4106021) baseStart_4106021 baseEnd_4106021 := by
    simpa [prefixWord, tailWord_4106021, baseEnd_4106021] using wordTrace_append hprefix tailTrace_4106021
  have hstable : (prefixWord ++ tailWord_4106021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106021).length < 2 ^ (prefixWord ++ tailWord_4106021).sum := by decide
  have hdescent : baseEnd_4106021 < baseStart_4106021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106058 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_4106058 : Nat := 118140960795 + 4106058 * 2 ^ 59
def prefixEnd_4106058 : Nat := 4983230072969 + 3 ^ 40 * 4106058 * 2
def baseEnd_4106058 : Nat := 2108381349239001262891589

theorem tailTrace_4106058 : CollatzResearch.WordTrace tailWord_4106058 prefixEnd_4106058 2108381349239001262891589 := by
  unfold tailWord_4106058
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440059639615149930359707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99840159038973733147625885 37440059639615149930359707)
  ·
    refine ⟨56160089459422724895539561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37440059639615149930359707 56160089459422724895539561)
    ·
      refine ⟨42120067094567043671654671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56160089459422724895539561 42120067094567043671654671)
      ·
        refine ⟨63180100641850565507482007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42120067094567043671654671 63180100641850565507482007)
        ·
          refine ⟨94770150962775848261223011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63180100641850565507482007 94770150962775848261223011)
          ·
            refine ⟨142155226444163772391834517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94770150962775848261223011 142155226444163772391834517)
            ·
              refine ⟨6663526239570176830867243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142155226444163772391834517 6663526239570176830867243)
              ·
                refine ⟨9995289359355265246300865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663526239570176830867243 9995289359355265246300865)
                ·
                  refine ⟨7496467019516448934725649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9995289359355265246300865 7496467019516448934725649)
                  ·
                    refine ⟨5622350264637336701044237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7496467019516448934725649 5622350264637336701044237)
                    ·
                      refine ⟨2108381349239001262891589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5622350264637336701044237 2108381349239001262891589)
                      ·
                        rfl

theorem cell23_4106058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_4106058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106058 prefixEnd_4106058 := by exact prefixLift 4106058
  have htrace : WordTrace (prefixWord ++ tailWord_4106058) baseStart_4106058 baseEnd_4106058 := by
    simpa [prefixWord, tailWord_4106058, baseEnd_4106058] using wordTrace_append hprefix tailTrace_4106058
  have hstable : (prefixWord ++ tailWord_4106058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106058).length < 2 ^ (prefixWord ++ tailWord_4106058).sum := by decide
  have hdescent : baseEnd_4106058 < baseStart_4106058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106064 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_4106064 : Nat := 118140960795 + 4106064 * 2 ^ 59
def prefixEnd_4106064 : Nat := 4983230072969 + 3 ^ 40 * 4106064 * 2
def baseEnd_4106064 : Nat := 2108384430122928239416561

theorem tailTrace_4106064 : CollatzResearch.WordTrace tailWord_4106064 prefixEnd_4106064 2108384430122928239416561 := by
  unfold tailWord_4106064
  simp only [CollatzResearch.WordTrace]
  refine ⟨74880228698219431373078623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99840304930959241830771497 74880228698219431373078623)
  ·
    refine ⟨112320343047329147059617935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74880228698219431373078623 112320343047329147059617935)
    ·
      refine ⟨168480514570993720589426903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112320343047329147059617935 168480514570993720589426903)
      ·
        refine ⟨252720771856490580884140355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168480514570993720589426903 252720771856490580884140355)
        ·
          refine ⟨379081157784735871326210533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252720771856490580884140355 379081157784735871326210533)
          ·
            refine ⟨71077717084637975873664475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379081157784735871326210533 71077717084637975873664475)
            ·
              refine ⟨106616575626956963810496713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71077717084637975873664475 106616575626956963810496713)
              ·
                refine ⟨79962431720217722857872535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106616575626956963810496713 79962431720217722857872535)
                ·
                  refine ⟨119943647580326584286808803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79962431720217722857872535 119943647580326584286808803)
                  ·
                    refine ⟨179915471370489876430213205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119943647580326584286808803 179915471370489876430213205)
                    ·
                      refine ⟨2108384430122928239416561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 179915471370489876430213205 2108384430122928239416561)
                      ·
                        rfl

theorem cell23_4106064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_4106064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106064 prefixEnd_4106064 := by exact prefixLift 4106064
  have htrace : WordTrace (prefixWord ++ tailWord_4106064) baseStart_4106064 baseEnd_4106064 := by
    simpa [prefixWord, tailWord_4106064, baseEnd_4106064] using wordTrace_append hprefix tailTrace_4106064
  have hstable : (prefixWord ++ tailWord_4106064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106064).length < 2 ^ (prefixWord ++ tailWord_4106064).sum := by decide
  have hdescent : baseEnd_4106064 < baseStart_4106064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106082 : List Nat := [3, 3, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_4106082 : Nat := 118140960795 + 4106082 * 2 ^ 59
def prefixEnd_4106082 : Nat := 4983230072969 + 3 ^ 40 * 4106082 * 2
def baseEnd_4106082 : Nat := 702797890924903056330493

theorem tailTrace_4106082 : CollatzResearch.WordTrace tailWord_4106082 prefixEnd_4106082 702797890924903056330493 := by
  unfold tailWord_4106082
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440278477593412955078125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99840742606915767880208333 37440278477593412955078125)
  ·
    refine ⟨14040104429097529858154297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37440278477593412955078125 14040104429097529858154297)
    ·
      refine ⟨10530078321823147393615723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14040104429097529858154297 10530078321823147393615723)
      ·
        refine ⟨15795117482734721090423585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10530078321823147393615723 15795117482734721090423585)
        ·
          refine ⟨11846338112051040817817689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15795117482734721090423585 11846338112051040817817689)
          ·
            refine ⟨8884753584038280613363267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11846338112051040817817689 8884753584038280613363267)
            ·
              refine ⟨13327130376057420920044901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884753584038280613363267 13327130376057420920044901)
              ·
                refine ⟨2498836945510766422508419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13327130376057420920044901 2498836945510766422508419)
                ·
                  refine ⟨3748255418266149633762629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498836945510766422508419 3748255418266149633762629)
                  ·
                    refine ⟨702797890924903056330493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3748255418266149633762629 702797890924903056330493)
                    ·
                      rfl

theorem cell23_4106082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_4106082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106082 prefixEnd_4106082 := by exact prefixLift 4106082
  have htrace : WordTrace (prefixWord ++ tailWord_4106082) baseStart_4106082 baseEnd_4106082 := by
    simpa [prefixWord, tailWord_4106082, baseEnd_4106082] using wordTrace_append hprefix tailTrace_4106082
  have hstable : (prefixWord ++ tailWord_4106082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106082).length < 2 ^ (prefixWord ++ tailWord_4106082).sum := by decide
  have hdescent : baseEnd_4106082 < baseStart_4106082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106098 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_4106098 : Nat := 118140960795 + 4106098 * 2 ^ 59
def prefixEnd_4106098 : Nat := 4983230072969 + 3 ^ 40 * 4106098 * 2
def baseEnd_4106098 : Nat := 2108401888465181106391405

theorem tailTrace_4106098 : CollatzResearch.WordTrace tailWord_4106098 prefixEnd_4106098 2108401888465181106391405 := by
  unfold tailWord_4106098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440424369578921638223737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99841131652210457701929965 37440424369578921638223737)
  ·
    refine ⟨28080318277184191228667803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37440424369578921638223737 28080318277184191228667803)
    ·
      refine ⟨42120477415776286843001705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28080318277184191228667803 42120477415776286843001705)
      ·
        refine ⟨31590358061832215132251279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42120477415776286843001705 31590358061832215132251279)
        ·
          refine ⟨47385537092748322698376919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31590358061832215132251279 47385537092748322698376919)
          ·
            refine ⟨71078305639122484047565379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47385537092748322698376919 71078305639122484047565379)
            ·
              refine ⟨106617458458683726071348069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71078305639122484047565379 106617458458683726071348069)
              ·
                refine ⟨19990773461003198638377763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106617458458683726071348069 19990773461003198638377763)
                ·
                  refine ⟨29986160191504797957566645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19990773461003198638377763 29986160191504797957566645)
                  ·
                    refine ⟨2811202517953574808521873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29986160191504797957566645 2811202517953574808521873)
                    ·
                      refine ⟨2108401888465181106391405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811202517953574808521873 2108401888465181106391405)
                      ·
                        rfl

theorem cell23_4106098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_4106098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106098 prefixEnd_4106098 := by exact prefixLift 4106098
  have htrace : WordTrace (prefixWord ++ tailWord_4106098) baseStart_4106098 baseEnd_4106098 := by
    simpa [prefixWord, tailWord_4106098, baseEnd_4106098] using wordTrace_append hprefix tailTrace_4106098
  have hstable : (prefixWord ++ tailWord_4106098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106098).length < 2 ^ (prefixWord ++ tailWord_4106098).sum := by decide
  have hdescent : baseEnd_4106098 < baseStart_4106098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106101 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4106101 : Nat := 118140960795 + 4106101 * 2 ^ 59
def prefixEnd_4106101 : Nat := 4983230072969 + 3 ^ 40 * 4106101 * 2
def baseEnd_4106101 : Nat := 2108403428907144594653891

theorem tailTrace_4106101 : CollatzResearch.WordTrace tailWord_4106101 prefixEnd_4106101 2108403428907144594653891 := by
  unfold tailWord_4106101
  simp only [CollatzResearch.WordTrace]
  refine ⟨149761806897304818065254157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99841204598203212043502771 149761806897304818065254157)
  ·
    refine ⟨56160677586489306774470309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149761806897304818065254157 56160677586489306774470309)
    ·
      refine ⟨10530127047466745020213183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56160677586489306774470309 10530127047466745020213183)
      ·
        refine ⟨15795190571200117530319775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10530127047466745020213183 15795190571200117530319775)
        ·
          refine ⟨23692785856800176295479663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15795190571200117530319775 23692785856800176295479663)
          ·
            refine ⟨35539178785200264443219495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23692785856800176295479663 35539178785200264443219495)
            ·
              refine ⟨53308768177800396664829243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35539178785200264443219495 53308768177800396664829243)
              ·
                refine ⟨79963152266700594997243865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53308768177800396664829243 79963152266700594997243865)
                ·
                  refine ⟨59972364200025446247932899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79963152266700594997243865 59972364200025446247932899)
                  ·
                    refine ⟨89958546300038169371899349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59972364200025446247932899 89958546300038169371899349)
                    ·
                      refine ⟨2108403428907144594653891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89958546300038169371899349 2108403428907144594653891)
                      ·
                        rfl

theorem cell23_4106101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4106101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106101 prefixEnd_4106101 := by exact prefixLift 4106101
  have htrace : WordTrace (prefixWord ++ tailWord_4106101) baseStart_4106101 baseEnd_4106101 := by
    simpa [prefixWord, tailWord_4106101, baseEnd_4106101] using wordTrace_append hprefix tailTrace_4106101
  have hstable : (prefixWord ++ tailWord_4106101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106101).length < 2 ^ (prefixWord ++ tailWord_4106101).sum := by decide
  have hdescent : baseEnd_4106101 < baseStart_4106101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106115 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 2, 3, 2]
def baseStart_4106115 : Nat := 118140960795 + 4106115 * 2 ^ 59
def prefixEnd_4106115 : Nat := 4983230072969 + 3 ^ 40 * 4106115 * 2
def baseEnd_4106115 : Nat := 2108410617636307539878827

theorem tailTrace_4106115 : CollatzResearch.WordTrace tailWord_4106115 prefixEnd_4106115 2108410617636307539878827 := by
  unfold tailWord_4106115
  simp only [CollatzResearch.WordTrace]
  refine ⟨149762317519254098456263799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99841545012836065637509199 149762317519254098456263799)
  ·
    refine ⟨224643476278881147684395699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149762317519254098456263799 224643476278881147684395699)
    ·
      refine ⟨336965214418321721526593549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224643476278881147684395699 336965214418321721526593549)
      ·
        refine ⟨126361955406870645572472581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336965214418321721526593549 126361955406870645572472581)
        ·
          refine ⟨23692866638788246044838609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126361955406870645572472581 23692866638788246044838609)
          ·
            refine ⟨17769649979091184533628957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23692866638788246044838609 17769649979091184533628957)
            ·
              refine ⟨6663618742159194200110859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17769649979091184533628957 6663618742159194200110859)
              ·
                refine ⟨9995428113238791300166289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663618742159194200110859 9995428113238791300166289)
                ·
                  refine ⟨7496571084929093475124717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9995428113238791300166289 7496571084929093475124717)
                  ·
                    refine ⟨2811214156848410053171769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7496571084929093475124717 2811214156848410053171769)
                    ·
                      refine ⟨2108410617636307539878827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811214156848410053171769 2108410617636307539878827)
                      ·
                        rfl

theorem cell23_4106115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_4106115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106115 prefixEnd_4106115 := by exact prefixLift 4106115
  have htrace : WordTrace (prefixWord ++ tailWord_4106115) baseStart_4106115 baseEnd_4106115 := by
    simpa [prefixWord, tailWord_4106115, baseEnd_4106115] using wordTrace_append hprefix tailTrace_4106115
  have hstable : (prefixWord ++ tailWord_4106115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106115).length < 2 ^ (prefixWord ++ tailWord_4106115).sum := by decide
  have hdescent : baseEnd_4106115 < baseStart_4106115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106121 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 1, 6]
def baseStart_4106121 : Nat := 118140960795 + 4106121 * 2 ^ 59
def prefixEnd_4106121 : Nat := 4983230072969 + 3 ^ 40 * 4106121 * 2
def baseEnd_4106121 : Nat := 702804566173411505467933

theorem tailTrace_4106121 : CollatzResearch.WordTrace tailWord_4106121 prefixEnd_4106121 702804566173411505467933 := by
  unfold tailWord_4106121
  simp only [CollatzResearch.WordTrace]
  refine ⟨149762536357232361480982217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99841690904821574320654811 149762536357232361480982217)
  ·
    refine ⟨112321902267924271110736663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149762536357232361480982217 112321902267924271110736663)
    ·
      refine ⟨168482853401886406666104995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112321902267924271110736663 168482853401886406666104995)
      ·
        refine ⟨252724280102829609999157493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168482853401886406666104995 252724280102829609999157493)
        ·
          refine ⟨23692901259640275937421015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252724280102829609999157493 23692901259640275937421015)
          ·
            refine ⟨35539351889460413906131523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23692901259640275937421015 35539351889460413906131523)
            ·
              refine ⟨53309027834190620859197285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35539351889460413906131523 53309027834190620859197285)
              ·
                refine ⟨9995442718910741411099491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53309027834190620859197285 9995442718910741411099491)
                ·
                  refine ⟨14993164078366112116649237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9995442718910741411099491 14993164078366112116649237)
                  ·
                    refine ⟨702804566173411505467933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14993164078366112116649237 702804566173411505467933)
                    ·
                      rfl

theorem cell23_4106121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_4106121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106121 prefixEnd_4106121 := by exact prefixLift 4106121
  have htrace : WordTrace (prefixWord ++ tailWord_4106121) baseStart_4106121 baseEnd_4106121 := by
    simpa [prefixWord, tailWord_4106121, baseEnd_4106121] using wordTrace_append hprefix tailTrace_4106121
  have hstable : (prefixWord ++ tailWord_4106121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106121).length < 2 ^ (prefixWord ++ tailWord_4106121).sum := by decide
  have hdescent : baseEnd_4106121 < baseStart_4106121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106148 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_4106148 : Nat := 118140960795 + 4106148 * 2 ^ 59
def prefixEnd_4106148 : Nat := 4983230072969 + 3 ^ 40 * 4106148 * 2
def baseEnd_4106148 : Nat := 2108427562497905910766175

theorem tailTrace_4106148 : CollatzResearch.WordTrace tailWord_4106148 prefixEnd_4106148 2108427562497905910766175 := by
  unfold tailWord_4106148
  simp only [CollatzResearch.WordTrace]
  refine ⟨74881760564067272546107549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99842347418756363394810065 74881760564067272546107549)
  ·
    refine ⟨28080660211525227204790331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74881760564067272546107549 28080660211525227204790331)
    ·
      refine ⟨42120990317287840807185497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28080660211525227204790331 42120990317287840807185497)
      ·
        refine ⟨31590742737965880605389123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42120990317287840807185497 31590742737965880605389123)
        ·
          refine ⟨47386114106948820908083685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31590742737965880605389123 47386114106948820908083685)
          ·
            refine ⟨8884896395052903920265691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47386114106948820908083685 8884896395052903920265691)
            ·
              refine ⟨13327344592579355880398537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884896395052903920265691 13327344592579355880398537)
              ·
                refine ⟨9995508444434516910298903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13327344592579355880398537 9995508444434516910298903)
                ·
                  refine ⟨14993262666651775365448355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9995508444434516910298903 14993262666651775365448355)
                  ·
                    refine ⟨22489893999977663048172533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14993262666651775365448355 22489893999977663048172533)
                    ·
                      refine ⟨2108427562497905910766175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22489893999977663048172533 2108427562497905910766175)
                      ·
                        rfl

theorem cell23_4106148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_4106148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106148 prefixEnd_4106148 := by exact prefixLift 4106148
  have htrace : WordTrace (prefixWord ++ tailWord_4106148) baseStart_4106148 baseEnd_4106148 := by
    simpa [prefixWord, tailWord_4106148, baseEnd_4106148] using wordTrace_append hprefix tailTrace_4106148
  have hstable : (prefixWord ++ tailWord_4106148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106148).length < 2 ^ (prefixWord ++ tailWord_4106148).sum := by decide
  have hdescent : baseEnd_4106148 < baseStart_4106148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106165 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_4106165 : Nat := 118140960795 + 4106165 * 2 ^ 59
def prefixEnd_4106165 : Nat := 4983230072969 + 3 ^ 40 * 4106165 * 2
def baseEnd_4106165 : Nat := 2108436291669032344253597

theorem tailTrace_4106165 : CollatzResearch.WordTrace tailWord_4106165 prefixEnd_4106165 2108436291669032344253597 := by
  unfold tailWord_4106165
  simp only [CollatzResearch.WordTrace]
  refine ⟨149764141169072956995583949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99842760779381971330389299 149764141169072956995583949)
  ·
    refine ⟨56161552938402358873343981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149764141169072956995583949 56161552938402358873343981)
    ·
      refine ⟨21060582351900884577503993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56161552938402358873343981 21060582351900884577503993)
      ·
        refine ⟨15795436763925663433127995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21060582351900884577503993 15795436763925663433127995)
        ·
          refine ⟨23693155145888495149691993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15795436763925663433127995 23693155145888495149691993)
          ·
            refine ⟨17769866359416371362268995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23693155145888495149691993 17769866359416371362268995)
            ·
              refine ⟨26654799539124557043403493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17769866359416371362268995 26654799539124557043403493)
              ·
                refine ⟨4997774913585854445638155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26654799539124557043403493 4997774913585854445638155)
                ·
                  refine ⟨7496662370378781668457233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997774913585854445638155 7496662370378781668457233)
                  ·
                    refine ⟨5622496777784086251342925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7496662370378781668457233 5622496777784086251342925)
                    ·
                      refine ⟨2108436291669032344253597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5622496777784086251342925 2108436291669032344253597)
                      ·
                        rfl

theorem cell23_4106165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_4106165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106165 prefixEnd_4106165 := by exact prefixLift 4106165
  have htrace : WordTrace (prefixWord ++ tailWord_4106165) baseStart_4106165 baseEnd_4106165 := by
    simpa [prefixWord, tailWord_4106165, baseEnd_4106165] using wordTrace_append hprefix tailTrace_4106165
  have hstable : (prefixWord ++ tailWord_4106165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106165).length < 2 ^ (prefixWord ++ tailWord_4106165).sum := by decide
  have hdescent : baseEnd_4106165 < baseStart_4106165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106191 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_4106191 : Nat := 118140960795 + 4106191 * 2 ^ 59
def prefixEnd_4106191 : Nat := 4983230072969 + 3 ^ 40 * 4106191 * 2
def baseEnd_4106191 : Nat := 2108449642166049242528477

theorem tailTrace_4106191 : CollatzResearch.WordTrace tailWord_4106191 prefixEnd_4106191 2108449642166049242528477 := by
  unfold tailWord_4106191
  simp only [CollatzResearch.WordTrace]
  refine ⟨149765089466978763436030427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99843392977985842290686951 149765089466978763436030427)
  ·
    refine ⟨224647634200468145154045641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149765089466978763436030427 224647634200468145154045641)
    ·
      refine ⟨168485725650351108865534231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224647634200468145154045641 168485725650351108865534231)
      ·
        refine ⟨252728588475526663298301347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168485725650351108865534231 252728588475526663298301347)
        ·
          refine ⟨379092882713289994947452021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252728588475526663298301347 379092882713289994947452021)
          ·
            refine ⟨35539957754370937026323627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379092882713289994947452021 35539957754370937026323627)
            ·
              refine ⟨53309936631556405539485441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35539957754370937026323627 53309936631556405539485441)
              ·
                refine ⟨39982452473667304154614081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53309936631556405539485441 39982452473667304154614081)
                ·
                  refine ⟨29986839355250478115960561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39982452473667304154614081 29986839355250478115960561)
                  ·
                    refine ⟨22490129516437858586970421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29986839355250478115960561 22490129516437858586970421)
                    ·
                      refine ⟨2108449642166049242528477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22490129516437858586970421 2108449642166049242528477)
                      ·
                        rfl

theorem cell23_4106191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_4106191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106191 prefixEnd_4106191 := by exact prefixLift 4106191
  have htrace : WordTrace (prefixWord ++ tailWord_4106191) baseStart_4106191 baseEnd_4106191 := by
    simpa [prefixWord, tailWord_4106191, baseEnd_4106191] using wordTrace_append hprefix tailTrace_4106191
  have hstable : (prefixWord ++ tailWord_4106191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106191).length < 2 ^ (prefixWord ++ tailWord_4106191).sum := by decide
  have hdescent : baseEnd_4106191 < baseStart_4106191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106196 : List Nat := [2, 4, 1, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_4106196 : Nat := 118140960795 + 4106196 * 2 ^ 59
def prefixEnd_4106196 : Nat := 4983230072969 + 3 ^ 40 * 4106196 * 2
def baseEnd_4106196 : Nat := 2108452209569321722965955

theorem tailTrace_4106196 : CollatzResearch.WordTrace tailWord_4106196 prefixEnd_4106196 2108452209569321722965955 := by
  unfold tailWord_4106196
  simp only [CollatzResearch.WordTrace]
  refine ⟨74882635915980324644981221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99843514554640432859974961 74882635915980324644981221)
  ·
    refine ⟨14040494234246310870933979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74882635915980324644981221 14040494234246310870933979)
    ·
      refine ⟨21060741351369466306400969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14040494234246310870933979 21060741351369466306400969)
      ·
        refine ⟨15795556013527099729800727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21060741351369466306400969 15795556013527099729800727)
        ·
          refine ⟨23693334020290649594701091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15795556013527099729800727 23693334020290649594701091)
          ·
            refine ⟨35540001030435974392051637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23693334020290649594701091 35540001030435974392051637)
            ·
              refine ⟨3331875096603372599254841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35540001030435974392051637 3331875096603372599254841)
              ·
                refine ⟨2498906322452529449441131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3331875096603372599254841 2498906322452529449441131)
                ·
                  refine ⟨3748359483678794174161697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498906322452529449441131 3748359483678794174161697)
                  ·
                    refine ⟨2811269612759095630621273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3748359483678794174161697 2811269612759095630621273)
                    ·
                      refine ⟨2108452209569321722965955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811269612759095630621273 2108452209569321722965955)
                      ·
                        rfl

theorem cell23_4106196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_4106196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106196 prefixEnd_4106196 := by exact prefixLift 4106196
  have htrace : WordTrace (prefixWord ++ tailWord_4106196) baseStart_4106196 baseEnd_4106196 := by
    simpa [prefixWord, tailWord_4106196, baseEnd_4106196] using wordTrace_append hprefix tailTrace_4106196
  have hstable : (prefixWord ++ tailWord_4106196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106196).length < 2 ^ (prefixWord ++ tailWord_4106196).sum := by decide
  have hdescent : baseEnd_4106196 < baseStart_4106196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106222 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_4106222 : Nat := 118140960795 + 4106222 * 2 ^ 59
def prefixEnd_4106222 : Nat := 4983230072969 + 3 ^ 40 * 4106222 * 2
def baseEnd_4106222 : Nat := 2108465560066338621240835

theorem tailTrace_4106222 : CollatzResearch.WordTrace tailWord_4106222 prefixEnd_4106222 2108465560066338621240835 := by
  unfold tailWord_4106222
  simp only [CollatzResearch.WordTrace]
  refine ⟨18720777516233306966301115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99844146753244303820272613 18720777516233306966301115)
  ·
    refine ⟨28081166274349960449451673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18720777516233306966301115 28081166274349960449451673)
    ·
      refine ⟨21060874705762470337088755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28081166274349960449451673 21060874705762470337088755)
      ·
        refine ⟨31591312058643705505633133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21060874705762470337088755 31591312058643705505633133)
        ·
          refine ⟨11846742021991389564612425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31591312058643705505633133 11846742021991389564612425)
          ·
            refine ⟨8885056516493542173459319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11846742021991389564612425 8885056516493542173459319)
            ·
              refine ⟨13327584774740313260188979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885056516493542173459319 13327584774740313260188979)
              ·
                refine ⟨19991377162110469890283469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13327584774740313260188979 19991377162110469890283469)
                ·
                  refine ⟨7496766435791426208856301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19991377162110469890283469 7496766435791426208856301)
                  ·
                    refine ⟨2811287413421784828321113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7496766435791426208856301 2811287413421784828321113)
                    ·
                      refine ⟨2108465560066338621240835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811287413421784828321113 2108465560066338621240835)
                      ·
                        rfl

theorem cell23_4106222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_4106222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106222 prefixEnd_4106222 := by exact prefixLift 4106222
  have htrace : WordTrace (prefixWord ++ tailWord_4106222) baseStart_4106222 baseEnd_4106222 := by
    simpa [prefixWord, tailWord_4106222, baseEnd_4106222] using wordTrace_append hprefix tailTrace_4106222
  have hstable : (prefixWord ++ tailWord_4106222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106222).length < 2 ^ (prefixWord ++ tailWord_4106222).sum := by decide
  have hdescent : baseEnd_4106222 < baseStart_4106222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106235 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 6, 2, 2]
def baseStart_4106235 : Nat := 118140960795 + 4106235 * 2 ^ 59
def prefixEnd_4106235 : Nat := 4983230072969 + 3 ^ 40 * 4106235 * 2
def baseEnd_4106235 : Nat := 2108472235314847070378275

theorem tailTrace_4106235 : CollatzResearch.WordTrace tailWord_4106235 prefixEnd_4106235 2108472235314847070378275 := by
  unfold tailWord_4106235
  simp only [CollatzResearch.WordTrace]
  refine ⟨149766694278819358950632159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99844462852546239300421439 149766694278819358950632159)
  ·
    refine ⟨224650041418229038425948239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149766694278819358950632159 224650041418229038425948239)
    ·
      refine ⟨336975062127343557638922359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224650041418229038425948239 336975062127343557638922359)
      ·
        refine ⟨505462593191015336458383539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336975062127343557638922359 505462593191015336458383539)
        ·
          refine ⟨758193889786523004687575309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505462593191015336458383539 758193889786523004687575309)
          ·
            refine ⟨284322708669946126757840741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 758193889786523004687575309 284322708669946126757840741)
            ·
              refine ⟨53310507875614898767095139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284322708669946126757840741 53310507875614898767095139)
              ·
                refine ⟨79965761813422348150642709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53310507875614898767095139 79965761813422348150642709)
                ·
                  refine ⟨3748395085004172569561377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79965761813422348150642709 3748395085004172569561377)
                  ·
                    refine ⟨2811296313753129427171033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3748395085004172569561377 2811296313753129427171033)
                    ·
                      refine ⟨2108472235314847070378275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811296313753129427171033 2108472235314847070378275)
                      ·
                        rfl

theorem cell23_4106235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 2, 2].length) (baseStart_4106235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106235 prefixEnd_4106235 := by exact prefixLift 4106235
  have htrace : WordTrace (prefixWord ++ tailWord_4106235) baseStart_4106235 baseEnd_4106235 := by
    simpa [prefixWord, tailWord_4106235, baseEnd_4106235] using wordTrace_append hprefix tailTrace_4106235
  have hstable : (prefixWord ++ tailWord_4106235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106235).length < 2 ^ (prefixWord ++ tailWord_4106235).sum := by decide
  have hdescent : baseEnd_4106235 < baseStart_4106235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106248 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_4106248 : Nat := 118140960795 + 4106248 * 2 ^ 59
def prefixEnd_4106248 : Nat := 4983230072969 + 3 ^ 40 * 4106248 * 2
def baseEnd_4106248 : Nat := 2108478910563355519515715

theorem tailTrace_4106248 : CollatzResearch.WordTrace tailWord_4106248 prefixEnd_4106248 2108478910563355519515715 := by
  unfold tailWord_4106248
  simp only [CollatzResearch.WordTrace]
  refine ⟨74883584213886131085427699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99844778951848174780570265 74883584213886131085427699)
  ·
    refine ⟨112325376320829196628141549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74883584213886131085427699 112325376320829196628141549)
    ·
      refine ⟨42122016120310948735553081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112325376320829196628141549 42122016120310948735553081)
      ·
        refine ⟨31591512090233211551664811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42122016120310948735553081 31591512090233211551664811)
        ·
          refine ⟨47387268135349817327497217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31591512090233211551664811 47387268135349817327497217)
          ·
            refine ⟨35540451101512362995622913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47387268135349817327497217 35540451101512362995622913)
            ·
              refine ⟨26655338326134272246717185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35540451101512362995622913 26655338326134272246717185)
              ·
                refine ⟨19991503744600704185037889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26655338326134272246717185 19991503744600704185037889)
                ·
                  refine ⟨14993627808450528138778417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19991503744600704185037889 14993627808450528138778417)
                  ·
                    refine ⟨11245220856337896104083813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14993627808450528138778417 11245220856337896104083813)
                    ·
                      refine ⟨2108478910563355519515715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11245220856337896104083813 2108478910563355519515715)
                      ·
                        rfl

theorem cell23_4106248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_4106248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106248 prefixEnd_4106248 := by exact prefixLift 4106248
  have htrace : WordTrace (prefixWord ++ tailWord_4106248) baseStart_4106248 baseEnd_4106248 := by
    simpa [prefixWord, tailWord_4106248, baseEnd_4106248] using wordTrace_append hprefix tailTrace_4106248
  have hstable : (prefixWord ++ tailWord_4106248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106248).length < 2 ^ (prefixWord ++ tailWord_4106248).sum := by decide
  have hdescent : baseEnd_4106248 < baseStart_4106248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106269 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_4106269 : Nat := 118140960795 + 4106269 * 2 ^ 59
def prefixEnd_4106269 : Nat := 4983230072969 + 3 ^ 40 * 4106269 * 2
def baseEnd_4106269 : Nat := 2108489693657099937353119

theorem tailTrace_4106269 : CollatzResearch.WordTrace tailWord_4106269 prefixEnd_4106269 2108489693657099937353119 := by
  unfold tailWord_4106269
  simp only [CollatzResearch.WordTrace]
  refine ⟨149767934360696182757369861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99845289573797455171579907 149767934360696182757369861)
  ·
    refine ⟨28081487692630534267006849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149767934360696182757369861 28081487692630534267006849)
    ·
      refine ⟨21061115769472900700255137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28081487692630534267006849 21061115769472900700255137)
      ·
        refine ⟨15795836827104675525191353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21061115769472900700255137 15795836827104675525191353)
        ·
          refine ⟨11846877620328506643893515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15795836827104675525191353 11846877620328506643893515)
          ·
            refine ⟨17770316430492759965840273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11846877620328506643893515 17770316430492759965840273)
            ·
              refine ⟨13327737322869569974380205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17770316430492759965840273 13327737322869569974380205)
              ·
                refine ⟨4997901496076088740392577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13327737322869569974380205 4997901496076088740392577)
                ·
                  refine ⟨3748426122057066555294433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4997901496076088740392577 3748426122057066555294433)
                  ·
                    refine ⟨2811319591542799916470825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3748426122057066555294433 2811319591542799916470825)
                    ·
                      refine ⟨2108489693657099937353119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811319591542799916470825 2108489693657099937353119)
                      ·
                        rfl

theorem cell23_4106269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_4106269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106269 prefixEnd_4106269 := by exact prefixLift 4106269
  have htrace : WordTrace (prefixWord ++ tailWord_4106269) baseStart_4106269 baseEnd_4106269 := by
    simpa [prefixWord, tailWord_4106269, baseEnd_4106269] using wordTrace_append hprefix tailTrace_4106269
  have hstable : (prefixWord ++ tailWord_4106269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106269).length < 2 ^ (prefixWord ++ tailWord_4106269).sum := by decide
  have hdescent : baseEnd_4106269 < baseStart_4106269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106288 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 1, 7]
def baseStart_4106288 : Nat := 118140960795 + 4106288 * 2 ^ 59
def prefixEnd_4106288 : Nat := 4983230072969 + 3 ^ 40 * 4106288 * 2
def baseEnd_4106288 : Nat := 702833149929845121005177

theorem tailTrace_4106288 : CollatzResearch.WordTrace tailWord_4106288 prefixEnd_4106288 702833149929845121005177 := by
  unfold tailWord_4106288
  simp only [CollatzResearch.WordTrace]
  refine ⟨74884313673813674501155759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99845751565084899334874345 74884313673813674501155759)
  ·
    refine ⟨112326470510720511751733639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74884313673813674501155759 112326470510720511751733639)
    ·
      refine ⟨168489705766080767627600459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112326470510720511751733639 168489705766080767627600459)
      ·
        refine ⟨252734558649121151441400689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168489705766080767627600459 252734558649121151441400689)
        ·
          refine ⟨189550918986840863581050517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252734558649121151441400689 189550918986840863581050517)
          ·
            refine ⟨8885199327508165480361743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189550918986840863581050517 8885199327508165480361743)
            ·
              refine ⟨13327798991262248220542615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885199327508165480361743 13327798991262248220542615)
              ·
                refine ⟨19991698486893372330813923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13327798991262248220542615 19991698486893372330813923)
                ·
                  refine ⟨29987547730340058496220885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19991698486893372330813923 29987547730340058496220885)
                  ·
                    refine ⟨702833149929845121005177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29987547730340058496220885 702833149929845121005177)
                    ·
                      rfl

theorem cell23_4106288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_4106288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106288 prefixEnd_4106288 := by exact prefixLift 4106288
  have htrace : WordTrace (prefixWord ++ tailWord_4106288) baseStart_4106288 baseEnd_4106288 := by
    simpa [prefixWord, tailWord_4106288, baseEnd_4106288] using wordTrace_append hprefix tailTrace_4106288
  have hstable : (prefixWord ++ tailWord_4106288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106288).length < 2 ^ (prefixWord ++ tailWord_4106288).sum := by decide
  have hdescent : baseEnd_4106288 < baseStart_4106288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106345 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 3]
def baseStart_4106345 : Nat := 118140960795 + 4106345 * 2 ^ 59
def prefixEnd_4106345 : Nat := 4983230072969 + 3 ^ 40 * 4106345 * 2
def baseEnd_4106345 : Nat := 2108528718186841640002769

theorem tailTrace_4106345 : CollatzResearch.WordTrace tailWord_4106345 prefixEnd_4106345 2108528718186841640002769 := by
  unfold tailWord_4106345
  simp only [CollatzResearch.WordTrace]
  refine ⟨149770706308420847737136489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99847137538947231824757659 149770706308420847737136489)
  ·
    refine ⟨112328029731315635802852367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149770706308420847737136489 112328029731315635802852367)
    ·
      refine ⟨168492044596973453704278551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112328029731315635802852367 168492044596973453704278551)
      ·
        refine ⟨252738066895460180556417827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168492044596973453704278551 252738066895460180556417827)
        ·
          refine ⟨379107100343190270834626741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252738066895460180556417827 379107100343190270834626741)
          ·
            refine ⟨35541290657174087890746257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379107100343190270834626741 35541290657174087890746257)
            ·
              refine ⟨26655967992880565918059693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35541290657174087890746257 26655967992880565918059693)
              ·
                refine ⟨9995987997330212219272385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26655967992880565918059693 9995987997330212219272385)
                ·
                  refine ⟨7496990997997659164454289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9995987997330212219272385 7496990997997659164454289)
                  ·
                    refine ⟨5622743248498244373340717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7496990997997659164454289 5622743248498244373340717)
                    ·
                      refine ⟨2108528718186841640002769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5622743248498244373340717 2108528718186841640002769)
                      ·
                        rfl

theorem cell23_4106345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_4106345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106345 prefixEnd_4106345 := by exact prefixLift 4106345
  have htrace : WordTrace (prefixWord ++ tailWord_4106345) baseStart_4106345 baseEnd_4106345 := by
    simpa [prefixWord, tailWord_4106345, baseEnd_4106345] using wordTrace_append hprefix tailTrace_4106345
  have hstable : (prefixWord ++ tailWord_4106345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106345).length < 2 ^ (prefixWord ++ tailWord_4106345).sum := by decide
  have hdescent : baseEnd_4106345 < baseStart_4106345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106348 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 8]
def baseStart_4106348 : Nat := 118140960795 + 4106348 * 2 ^ 59
def prefixEnd_4106348 : Nat := 4983230072969 + 3 ^ 40 * 4106348 * 2
def baseEnd_4106348 : Nat := 234281139847645014251695

theorem tailTrace_4106348 : CollatzResearch.WordTrace tailWord_4106348 prefixEnd_4106348 234281139847645014251695 := by
  unfold tailWord_4106348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74885407863704989624747849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99847210484939986166330465 74885407863704989624747849)
  ·
    refine ⟨56164055897778742218560887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74885407863704989624747849 56164055897778742218560887)
    ·
      refine ⟨84246083846668113327841331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56164055897778742218560887 84246083846668113327841331)
      ·
        refine ⟨126369125770002169991761997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84246083846668113327841331 126369125770002169991761997)
        ·
          refine ⟨47388422163750813746910749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126369125770002169991761997 47388422163750813746910749)
          ·
            refine ⟨17770658311406555155091531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47388422163750813746910749 17770658311406555155091531)
            ·
              refine ⟨26655987467109832732637297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17770658311406555155091531 26655987467109832732637297)
              ·
                refine ⟨19991990600332374549477973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26655987467109832732637297 19991990600332374549477973)
                ·
                  refine ⟨234281139847645014251695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19991990600332374549477973 234281139847645014251695)
                  ·
                    rfl

theorem cell23_4106348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_4106348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106348 prefixEnd_4106348 := by exact prefixLift 4106348
  have htrace : WordTrace (prefixWord ++ tailWord_4106348) baseStart_4106348 baseEnd_4106348 := by
    simpa [prefixWord, tailWord_4106348, baseEnd_4106348] using wordTrace_append hprefix tailTrace_4106348
  have hstable : (prefixWord ++ tailWord_4106348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106348).length < 2 ^ (prefixWord ++ tailWord_4106348).sum := by decide
  have hdescent : baseEnd_4106348 < baseStart_4106348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106369 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 3, 4]
def baseStart_4106369 : Nat := 118140960795 + 4106369 * 2 ^ 59
def prefixEnd_4106369 : Nat := 4983230072969 + 3 ^ 40 * 4106369 * 2
def baseEnd_4106369 : Nat := 702847013907516515367553

theorem tailTrace_4106369 : CollatzResearch.WordTrace tailWord_4106369 prefixEnd_4106369 702847013907516515367553 := by
  unfold tailWord_4106369
  simp only [CollatzResearch.WordTrace]
  refine ⟨149771581660333899836010161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99847721106889266557340107 149771581660333899836010161)
  ·
    refine ⟨112328686245250424877007621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149771581660333899836010161 112328686245250424877007621)
    ·
      refine ⟨21061628670984454664438929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112328686245250424877007621 21061628670984454664438929)
      ·
        refine ⟨15796221503238340998329197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21061628670984454664438929 15796221503238340998329197)
        ·
          refine ⟨5923583063714377874373449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15796221503238340998329197 5923583063714377874373449)
          ·
            refine ⟨4442687297785783405780087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5923583063714377874373449 4442687297785783405780087)
            ·
              refine ⟨6664030946678675108670131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442687297785783405780087 6664030946678675108670131)
              ·
                refine ⟨9996046420018012663005197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664030946678675108670131 9996046420018012663005197)
                ·
                  refine ⟨3748517407506754748626949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9996046420018012663005197 3748517407506754748626949)
                  ·
                    refine ⟨702847013907516515367553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3748517407506754748626949 702847013907516515367553)
                    ·
                      rfl

theorem cell23_4106369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_4106369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106369 prefixEnd_4106369 := by exact prefixLift 4106369
  have htrace : WordTrace (prefixWord ++ tailWord_4106369) baseStart_4106369 baseEnd_4106369 := by
    simpa [prefixWord, tailWord_4106369, baseEnd_4106369] using wordTrace_append hprefix tailTrace_4106369
  have hstable : (prefixWord ++ tailWord_4106369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106369).length < 2 ^ (prefixWord ++ tailWord_4106369).sum := by decide
  have hdescent : baseEnd_4106369 < baseStart_4106369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106382 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_4106382 : Nat := 118140960795 + 4106382 * 2 ^ 59
def prefixEnd_4106382 : Nat := 4983230072969 + 3 ^ 40 * 4106382 * 2
def baseEnd_4106382 : Nat := 234283079663450888360011

theorem tailTrace_4106382 : CollatzResearch.WordTrace tailWord_4106382 prefixEnd_4106382 234283079663450888360011 := by
  unfold tailWord_4106382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18721506976160850382029175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99848037206191202037488933 18721506976160850382029175)
  ·
    refine ⟨28082260464241275573043763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18721506976160850382029175 28082260464241275573043763)
    ·
      refine ⟨42123390696361913359565645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28082260464241275573043763 42123390696361913359565645)
      ·
        refine ⟨15796271511135717509837117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42123390696361913359565645 15796271511135717509837117)
        ·
          refine ⟨5923601816675894066188919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15796271511135717509837117 5923601816675894066188919)
          ·
            refine ⟨8885402725013841099283379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923601816675894066188919 8885402725013841099283379)
            ·
              refine ⟨13328104087520761648925069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885402725013841099283379 13328104087520761648925069)
              ·
                refine ⟨4998039032820285618346901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13328104087520761648925069 4998039032820285618346901)
                ·
                  refine ⟨234283079663450888360011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4998039032820285618346901 234283079663450888360011)
                  ·
                    rfl

theorem cell23_4106382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_4106382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106382 prefixEnd_4106382 := by exact prefixLift 4106382
  have htrace : WordTrace (prefixWord ++ tailWord_4106382) baseStart_4106382 baseEnd_4106382 := by
    simpa [prefixWord, tailWord_4106382, baseEnd_4106382] using wordTrace_append hprefix tailTrace_4106382
  have hstable : (prefixWord ++ tailWord_4106382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106382).length < 2 ^ (prefixWord ++ tailWord_4106382).sum := by decide
  have hdescent : baseEnd_4106382 < baseStart_4106382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106420 : List Nat := [2, 5, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4106420 : Nat := 118140960795 + 4106420 * 2 ^ 59
def prefixEnd_4106420 : Nat := 4983230072969 + 3 ^ 40 * 4106420 * 2
def baseEnd_4106420 : Nat := 702855743078642948854975

theorem tailTrace_4106420 : CollatzResearch.WordTrace tailWord_4106420 prefixEnd_4106420 702855743078642948854975 := by
  unfold tailWord_4106420
  simp only [CollatzResearch.WordTrace]
  refine ⟨74886720891574567773058357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99848961188766090364077809 74886720891574567773058357)
  ·
    refine ⟨7020630083585115728724221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74886720891574567773058357 7020630083585115728724221)
    ·
      refine ⟨2632736281344418398271583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7020630083585115728724221 2632736281344418398271583)
      ·
        refine ⟨3949104422016627597407375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632736281344418398271583 3949104422016627597407375)
        ·
          refine ⟨5923656633024941396111063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949104422016627597407375 5923656633024941396111063)
          ·
            refine ⟨8885484949537412094166595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923656633024941396111063 8885484949537412094166595)
            ·
              refine ⟨13328227424306118141249893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885484949537412094166595 13328227424306118141249893)
              ·
                refine ⟨2499042642057397151484355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13328227424306118141249893 2499042642057397151484355)
                ·
                  refine ⟨3748563963086095727226533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499042642057397151484355 3748563963086095727226533)
                  ·
                    refine ⟨702855743078642948854975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3748563963086095727226533 702855743078642948854975)
                    ·
                      rfl

theorem cell23_4106420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4106420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106420 prefixEnd_4106420 := by exact prefixLift 4106420
  have htrace : WordTrace (prefixWord ++ tailWord_4106420) baseStart_4106420 baseEnd_4106420 := by
    simpa [prefixWord, tailWord_4106420, baseEnd_4106420] using wordTrace_append hprefix tailTrace_4106420
  have hstable : (prefixWord ++ tailWord_4106420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106420).length < 2 ^ (prefixWord ++ tailWord_4106420).sum := by decide
  have hdescent : baseEnd_4106420 < baseStart_4106420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106426 : List Nat := [3, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3]
def baseStart_4106426 : Nat := 118140960795 + 4106426 * 2 ^ 59
def prefixEnd_4106426 : Nat := 4983230072969 + 3 ^ 40 * 4106426 * 2
def baseEnd_4106426 : Nat := 2108570310119855823089897

theorem tailTrace_4106426 : CollatzResearch.WordTrace tailWord_4106426 prefixEnd_4106426 2108570310119855823089897 := by
  unfold tailWord_4106426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37443415155281849642708783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99849107080751599047223421 37443415155281849642708783)
  ·
    refine ⟨56165122732922774464063175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37443415155281849642708783 56165122732922774464063175)
    ·
      refine ⟨84247684099384161696094763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56165122732922774464063175 84247684099384161696094763)
      ·
        refine ⟨126371526149076242544142145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84247684099384161696094763 126371526149076242544142145)
        ·
          refine ⟨94778644611807181908106609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126371526149076242544142145 94778644611807181908106609)
          ·
            refine ⟨71083983458855386431079957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94778644611807181908106609 71083983458855386431079957)
            ·
              refine ⟨3332061724633846238956873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71083983458855386431079957 3332061724633846238956873)
              ·
                refine ⟨2499046293475384679217655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3332061724633846238956873 2499046293475384679217655)
                ·
                  refine ⟨3748569440213077018826483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499046293475384679217655 3748569440213077018826483)
                  ·
                    refine ⟨5622854160319615528239725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3748569440213077018826483 5622854160319615528239725)
                    ·
                      refine ⟨2108570310119855823089897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5622854160319615528239725 2108570310119855823089897)
                      ·
                        rfl

theorem cell23_4106426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3].length) (baseStart_4106426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106426 prefixEnd_4106426 := by exact prefixLift 4106426
  have htrace : WordTrace (prefixWord ++ tailWord_4106426) baseStart_4106426 baseEnd_4106426 := by
    simpa [prefixWord, tailWord_4106426, baseEnd_4106426] using wordTrace_append hprefix tailTrace_4106426
  have hstable : (prefixWord ++ tailWord_4106426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106426).length < 2 ^ (prefixWord ++ tailWord_4106426).sum := by decide
  have hdescent : baseEnd_4106426 < baseStart_4106426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106442 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_4106442 : Nat := 118140960795 + 4106442 * 2 ^ 59
def prefixEnd_4106442 : Nat := 4983230072969 + 3 ^ 40 * 4106442 * 2
def baseEnd_4106442 : Nat := 702859508603442586829941

theorem tailTrace_4106442 : CollatzResearch.WordTrace tailWord_4106442 prefixEnd_4106442 702859508603442586829941 := by
  unfold tailWord_4106442
  simp only [CollatzResearch.WordTrace]
  refine ⟨37443561047267358325854395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99849496126046288868945053 37443561047267358325854395)
  ·
    refine ⟨56165341570901037488781593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37443561047267358325854395 56165341570901037488781593)
    ·
      refine ⟨42124006178175778116586195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56165341570901037488781593 42124006178175778116586195)
      ·
        refine ⟨63186009267263667174879293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42124006178175778116586195 63186009267263667174879293)
        ·
          refine ⟨23694753475223875190579735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63186009267263667174879293 23694753475223875190579735)
          ·
            refine ⟨35542130212835812785869603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23694753475223875190579735 35542130212835812785869603)
            ·
              refine ⟨53313195319253719178804405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35542130212835812785869603 53313195319253719178804405)
              ·
                refine ⟨4998112061180036173012913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53313195319253719178804405 4998112061180036173012913)
                ·
                  refine ⟨3748584045885027129759685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4998112061180036173012913 3748584045885027129759685)
                  ·
                    refine ⟨702859508603442586829941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3748584045885027129759685 702859508603442586829941)
                    ·
                      rfl

theorem cell23_4106442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_4106442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106442 prefixEnd_4106442 := by exact prefixLift 4106442
  have htrace : WordTrace (prefixWord ++ tailWord_4106442) baseStart_4106442 baseEnd_4106442 := by
    simpa [prefixWord, tailWord_4106442, baseEnd_4106442] using wordTrace_append hprefix tailTrace_4106442
  have hstable : (prefixWord ++ tailWord_4106442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106442).length < 2 ^ (prefixWord ++ tailWord_4106442).sum := by decide
  have hdescent : baseEnd_4106442 < baseStart_4106442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106448 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_4106448 : Nat := 118140960795 + 4106448 * 2 ^ 59
def prefixEnd_4106448 : Nat := 4983230072969 + 3 ^ 40 * 4106448 * 2
def baseEnd_4106448 : Nat := 2108581606694254737014795

theorem tailTrace_4106448 : CollatzResearch.WordTrace tailWord_4106448 prefixEnd_4106448 2108581606694254737014795 := by
  unfold tailWord_4106448
  simp only [CollatzResearch.WordTrace]
  refine ⟨74887231513523848164067999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99849642018031797552090665 74887231513523848164067999)
  ·
    refine ⟨112330847270285772246101999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74887231513523848164067999 112330847270285772246101999)
    ·
      refine ⟨168496270905428658369152999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112330847270285772246101999 168496270905428658369152999)
      ·
        refine ⟨252744406358142987553729499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168496270905428658369152999 252744406358142987553729499)
        ·
          refine ⟨379116609537214481330594249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252744406358142987553729499 379116609537214481330594249)
          ·
            refine ⟨284337457152910860997945687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379116609537214481330594249 284337457152910860997945687)
            ·
              refine ⟨426506185729366291496918531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284337457152910860997945687 426506185729366291496918531)
              ·
                refine ⟨639759278594049437245377797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426506185729366291496918531 639759278594049437245377797)
                ·
                  refine ⟨119954864736384269483508337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 639759278594049437245377797 119954864736384269483508337)
                  ·
                    refine ⟨89966148552288202112631253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119954864736384269483508337 89966148552288202112631253)
                    ·
                      refine ⟨2108581606694254737014795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89966148552288202112631253 2108581606694254737014795)
                      ·
                        rfl

theorem cell23_4106448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_4106448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106448 prefixEnd_4106448 := by exact prefixLift 4106448
  have htrace : WordTrace (prefixWord ++ tailWord_4106448) baseStart_4106448 baseEnd_4106448 := by
    simpa [prefixWord, tailWord_4106448, baseEnd_4106448] using wordTrace_append hprefix tailTrace_4106448
  have hstable : (prefixWord ++ tailWord_4106448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106448).length < 2 ^ (prefixWord ++ tailWord_4106448).sum := by decide
  have hdescent : baseEnd_4106448 < baseStart_4106448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106453 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_4106453 : Nat := 118140960795 + 4106453 * 2 ^ 59
def prefixEnd_4106453 : Nat := 4983230072969 + 3 ^ 40 * 4106453 * 2
def baseEnd_4106453 : Nat := 2108584174097527217452273

theorem tailTrace_4106453 : CollatzResearch.WordTrace tailWord_4106453 prefixEnd_4106453 2108584174097527217452273 := by
  unfold tailWord_4106453
  simp only [CollatzResearch.WordTrace]
  refine ⟨149774645392029582182068013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99849763594686388121378675 149774645392029582182068013)
  ·
    refine ⟨56165492022011093318275505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149774645392029582182068013 56165492022011093318275505)
    ·
      refine ⟨42124119016508319988706629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56165492022011093318275505 42124119016508319988706629)
      ·
        refine ⟨7898272315595309997882493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42124119016508319988706629 7898272315595309997882493)
        ·
          refine ⟨2961852118348241249205935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7898272315595309997882493 2961852118348241249205935)
          ·
            refine ⟨4442778177522361873808903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961852118348241249205935 4442778177522361873808903)
            ·
              refine ⟨6664167266283542810713355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442778177522361873808903 6664167266283542810713355)
              ·
                refine ⟨9996250899425314216070033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664167266283542810713355 9996250899425314216070033)
                ·
                  refine ⟨7497188174568985662052525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9996250899425314216070033 7497188174568985662052525)
                  ·
                    refine ⟨2811445565463369623269697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7497188174568985662052525 2811445565463369623269697)
                    ·
                      refine ⟨2108584174097527217452273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811445565463369623269697 2108584174097527217452273)
                      ·
                        rfl

theorem cell23_4106453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_4106453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106453 prefixEnd_4106453 := by exact prefixLift 4106453
  have htrace : WordTrace (prefixWord ++ tailWord_4106453) baseStart_4106453 baseEnd_4106453 := by
    simpa [prefixWord, tailWord_4106453, baseEnd_4106453] using wordTrace_append hprefix tailTrace_4106453
  have hstable : (prefixWord ++ tailWord_4106453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106453).length < 2 ^ (prefixWord ++ tailWord_4106453).sum := by decide
  have hdescent : baseEnd_4106453 < baseStart_4106453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106460 : List Nat := [2, 2, 5, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4106460 : Nat := 118140960795 + 4106460 * 2 ^ 59
def prefixEnd_4106460 : Nat := 4983230072969 + 3 ^ 40 * 4106460 * 2
def baseEnd_4106460 : Nat := 2108587768462108690064741

theorem tailTrace_4106460 : CollatzResearch.WordTrace tailWord_4106460 prefixEnd_4106460 2108587768462108690064741 := by
  unfold tailWord_4106460
  simp only [CollatzResearch.WordTrace]
  refine ⟨74887450351502111188786417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99849933802002814918381889 74887450351502111188786417)
  ·
    refine ⟨56165587763626583391589813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74887450351502111188786417 56165587763626583391589813)
    ·
      refine ⟨5265523852839992192961545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56165587763626583391589813 5265523852839992192961545)
      ·
        refine ⟨3949142889629994144721159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5265523852839992192961545 3949142889629994144721159)
        ·
          refine ⟨5923714334444991217081739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949142889629994144721159 5923714334444991217081739)
          ·
            refine ⟨8885571501667486825622609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923714334444991217081739 8885571501667486825622609)
            ·
              refine ⟨6664178626250615119216957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8885571501667486825622609 6664178626250615119216957)
              ·
                refine ⟨2499066984843980669706359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6664178626250615119216957 2499066984843980669706359)
                ·
                  refine ⟨3748600477265971004559539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499066984843980669706359 3748600477265971004559539)
                  ·
                    refine ⟨5622900715898956506839309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3748600477265971004559539 5622900715898956506839309)
                    ·
                      refine ⟨2108587768462108690064741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5622900715898956506839309 2108587768462108690064741)
                      ·
                        rfl

theorem cell23_4106460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4106460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106460 prefixEnd_4106460 := by exact prefixLift 4106460
  have htrace : WordTrace (prefixWord ++ tailWord_4106460) baseStart_4106460 baseEnd_4106460 := by
    simpa [prefixWord, tailWord_4106460, baseEnd_4106460] using wordTrace_append hprefix tailTrace_4106460
  have hstable : (prefixWord ++ tailWord_4106460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106460).length < 2 ^ (prefixWord ++ tailWord_4106460).sum := by decide
  have hdescent : baseEnd_4106460 < baseStart_4106460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106469 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 3]
def baseStart_4106469 : Nat := 118140960795 + 4106469 * 2 ^ 59
def prefixEnd_4106469 : Nat := 4983230072969 + 3 ^ 40 * 4106469 * 2
def baseEnd_4106469 : Nat := 2108592389787999154852199

theorem tailTrace_4106469 : CollatzResearch.WordTrace tailWord_4106469 prefixEnd_4106469 2108592389787999154852199 := by
  unfold tailWord_4106469
  simp only [CollatzResearch.WordTrace]
  refine ⟨149775228959971616914650461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99850152639981077943100307 149775228959971616914650461)
  ·
    refine ⟨56165710859989356342993923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149775228959971616914650461 56165710859989356342993923)
    ·
      refine ⟨84248566289984034514490885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56165710859989356342993923 84248566289984034514490885)
      ·
        refine ⟨15796606179372006471467041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84248566289984034514490885 15796606179372006471467041)
        ·
          refine ⟨11847454634529004853600281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15796606179372006471467041 11847454634529004853600281)
          ·
            refine ⟨8885590975896753640200211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11847454634529004853600281 8885590975896753640200211)
            ·
              refine ⟨13328386463845130460300317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885590975896753640200211 13328386463845130460300317)
              ·
                refine ⟨4998144923941923922612619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13328386463845130460300317 4998144923941923922612619)
                ·
                  refine ⟨7497217385912885883918929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998144923941923922612619 7497217385912885883918929)
                  ·
                    refine ⟨5622913039434664412939197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7497217385912885883918929 5622913039434664412939197)
                    ·
                      refine ⟨2108592389787999154852199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5622913039434664412939197 2108592389787999154852199)
                      ·
                        rfl

theorem cell23_4106469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_4106469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106469 prefixEnd_4106469 := by exact prefixLift 4106469
  have htrace : WordTrace (prefixWord ++ tailWord_4106469) baseStart_4106469 baseEnd_4106469 := by
    simpa [prefixWord, tailWord_4106469, baseEnd_4106469] using wordTrace_append hprefix tailTrace_4106469
  have hstable : (prefixWord ++ tailWord_4106469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106469).length < 2 ^ (prefixWord ++ tailWord_4106469).sum := by decide
  have hdescent : baseEnd_4106469 < baseStart_4106469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106556 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_4106556 : Nat := 118140960795 + 4106556 * 2 ^ 59
def prefixEnd_4106556 : Nat := 4983230072969 + 3 ^ 40 * 4106556 * 2
def baseEnd_4106556 : Nat := 2108637062604940314464299

theorem tailTrace_4106556 : CollatzResearch.WordTrace tailWord_4106556 prefixEnd_4106556 2108637062604940314464299 := by
  unfold tailWord_4106556
  simp only [CollatzResearch.WordTrace]
  refine ⟨74889201055328215386533761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99852268073770953848711681 74889201055328215386533761)
  ·
    refine ⟨56166900791496161539900321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74889201055328215386533761 56166900791496161539900321)
    ·
      refine ⟨42125175593622121154925241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56166900791496161539900321 42125175593622121154925241)
      ·
        refine ⟨31593881695216590866193931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42125175593622121154925241 31593881695216590866193931)
        ·
          refine ⟨47390822542824886299290897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31593881695216590866193931 47390822542824886299290897)
          ·
            refine ⟨35543116907118664724468173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47390822542824886299290897 35543116907118664724468173)
            ·
              refine ⟨13328668840169499271675565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35543116907118664724468173 13328668840169499271675565)
              ·
                refine ⟨4998250815063562226878337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13328668840169499271675565 4998250815063562226878337)
                ·
                  refine ⟨3748688111297671670158753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4998250815063562226878337 3748688111297671670158753)
                  ·
                    refine ⟨2811516083473253752619065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3748688111297671670158753 2811516083473253752619065)
                    ·
                      refine ⟨2108637062604940314464299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811516083473253752619065 2108637062604940314464299)
                      ·
                        rfl

theorem cell23_4106556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_4106556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106556 prefixEnd_4106556 := by exact prefixLift 4106556
  have htrace : WordTrace (prefixWord ++ tailWord_4106556) baseStart_4106556 baseEnd_4106556 := by
    simpa [prefixWord, tailWord_4106556, baseEnd_4106556] using wordTrace_append hprefix tailTrace_4106556
  have hstable : (prefixWord ++ tailWord_4106556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106556).length < 2 ^ (prefixWord ++ tailWord_4106556).sum := by decide
  have hdescent : baseEnd_4106556 < baseStart_4106556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106599 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_4106599 : Nat := 118140960795 + 4106599 * 2 ^ 59
def prefixEnd_4106599 : Nat := 4983230072969 + 3 ^ 40 * 4106599 * 2
def baseEnd_4106599 : Nat := 2108659142273083646226601

theorem tailTrace_4106599 : CollatzResearch.WordTrace tailWord_4106599 prefixEnd_4106599 2108659142273083646226601 := by
  unfold tailWord_4106599
  simp only [CollatzResearch.WordTrace]
  refine ⟨149779970449500649116882851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99853313633000432744588567 149779970449500649116882851)
  ·
    refine ⟨224669955674250973675324277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149779970449500649116882851 224669955674250973675324277)
    ·
      refine ⟨21062808344461028782061651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224669955674250973675324277 21062808344461028782061651)
      ·
        refine ⟨31594212516691543173092477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21062808344461028782061651 31594212516691543173092477)
        ·
          refine ⟨11847829693759328689909679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31594212516691543173092477 11847829693759328689909679)
          ·
            refine ⟨17771744540638993034864519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11847829693759328689909679 17771744540638993034864519)
            ·
              refine ⟨26657616810958489552296779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17771744540638993034864519 26657616810958489552296779)
              ·
                refine ⟨39986425216437734328445169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26657616810958489552296779 39986425216437734328445169)
                ·
                  refine ⟨29989818912328300746333877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39986425216437734328445169 29989818912328300746333877)
                  ·
                    refine ⟨2811545523030778194968801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29989818912328300746333877 2811545523030778194968801)
                    ·
                      refine ⟨2108659142273083646226601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811545523030778194968801 2108659142273083646226601)
                      ·
                        rfl

theorem cell23_4106599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_4106599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106599 prefixEnd_4106599 := by exact prefixLift 4106599
  have htrace : WordTrace (prefixWord ++ tailWord_4106599) baseStart_4106599 baseEnd_4106599 := by
    simpa [prefixWord, tailWord_4106599, baseEnd_4106599] using wordTrace_append hprefix tailTrace_4106599
  have hstable : (prefixWord ++ tailWord_4106599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106599).length < 2 ^ (prefixWord ++ tailWord_4106599).sum := by decide
  have hdescent : baseEnd_4106599 < baseStart_4106599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106626 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4106626 : Nat := 118140960795 + 4106626 * 2 ^ 59
def prefixEnd_4106626 : Nat := 4983230072969 + 3 ^ 40 * 4106626 * 2
def baseEnd_4106626 : Nat := 702891002083585013529659

theorem tailTrace_4106626 : CollatzResearch.WordTrace tailWord_4106626 prefixEnd_4106626 702891002083585013529659 := by
  unfold tailWord_4106626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37445238805100708182028933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99853970146935221818743821 37445238805100708182028933)
  ·
    refine ⟨7020982275956382784130425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37445238805100708182028933 7020982275956382784130425)
    ·
      refine ⟨5265736706967287088097819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7020982275956382784130425 5265736706967287088097819)
      ·
        refine ⟨7898605060450930632146729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5265736706967287088097819 7898605060450930632146729)
        ·
          refine ⟨5923953795338197974110047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7898605060450930632146729 5923953795338197974110047)
          ·
            refine ⟨8885930693007296961165071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923953795338197974110047 8885930693007296961165071)
            ·
              refine ⟨13328896039510945441747607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885930693007296961165071 13328896039510945441747607)
              ·
                refine ⟨19993344059266418162621411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13328896039510945441747607 19993344059266418162621411)
                ·
                  refine ⟨29990016088899627243932117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19993344059266418162621411 29990016088899627243932117)
                  ·
                    refine ⟨702891002083585013529659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29990016088899627243932117 702891002083585013529659)
                    ·
                      rfl

theorem cell23_4106626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4106626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106626 prefixEnd_4106626 := by exact prefixLift 4106626
  have htrace : WordTrace (prefixWord ++ tailWord_4106626) baseStart_4106626 baseEnd_4106626 := by
    simpa [prefixWord, tailWord_4106626, baseEnd_4106626] using wordTrace_append hprefix tailTrace_4106626
  have hstable : (prefixWord ++ tailWord_4106626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106626).length < 2 ^ (prefixWord ++ tailWord_4106626).sum := by decide
  have hdescent : baseEnd_4106626 < baseStart_4106626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106656 : List Nat := [2, 1, 1, 4, 1, 3, 2, 4, 1, 4]
def baseStart_4106656 : Nat := 118140960795 + 4106656 * 2 ^ 59
def prefixEnd_4106656 : Nat := 4983230072969 + 3 ^ 40 * 4106656 * 2
def baseEnd_4106656 : Nat := 702896136890129974404613

theorem tailTrace_4106656 : CollatzResearch.WordTrace tailWord_4106656 prefixEnd_4106656 702896136890129974404613 := by
  unfold tailWord_4106656
  simp only [CollatzResearch.WordTrace]
  refine ⟨74891024705147073925853911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99854699606862765234471881 74891024705147073925853911)
  ·
    refine ⟨112336537057720610888780867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74891024705147073925853911 112336537057720610888780867)
    ·
      refine ⟨168504805586580916333171301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112336537057720610888780867 168504805586580916333171301)
      ·
        refine ⟨31594651047483921812469619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168504805586580916333171301 31594651047483921812469619)
        ·
          refine ⟨47391976571225882718704429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31594651047483921812469619 47391976571225882718704429)
          ·
            refine ⟨17771991214209706019514161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47391976571225882718704429 17771991214209706019514161)
            ·
              refine ⟨13328993410657279514635621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17771991214209706019514161 13328993410657279514635621)
              ·
                refine ⟨2499186264498239908994179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13328993410657279514635621 2499186264498239908994179)
                ·
                  refine ⟨3748779396747359863491269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499186264498239908994179 3748779396747359863491269)
                  ·
                    refine ⟨702896136890129974404613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3748779396747359863491269 702896136890129974404613)
                    ·
                      rfl

theorem cell23_4106656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 4].length) (baseStart_4106656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106656 prefixEnd_4106656 := by exact prefixLift 4106656
  have htrace : WordTrace (prefixWord ++ tailWord_4106656) baseStart_4106656 baseEnd_4106656 := by
    simpa [prefixWord, tailWord_4106656, baseEnd_4106656] using wordTrace_append hprefix tailTrace_4106656
  have hstable : (prefixWord ++ tailWord_4106656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106656).length < 2 ^ (prefixWord ++ tailWord_4106656).sum := by decide
  have hdescent : baseEnd_4106656 < baseStart_4106656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106682 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_4106682 : Nat := 118140960795 + 4106682 * 2 ^ 59
def prefixEnd_4106682 : Nat := 4983230072969 + 3 ^ 40 * 4106682 * 2
def baseEnd_4106682 : Nat := 702900587055802273829573

theorem tailTrace_4106682 : CollatzResearch.WordTrace tailWord_4106682 prefixEnd_4106682 702900587055802273829573 := by
  unfold tailWord_4106682
  simp only [CollatzResearch.WordTrace]
  refine ⟨37445749427049988573038575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99855331805466636194769533 37445749427049988573038575)
  ·
    refine ⟨56168624140574982859557863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37445749427049988573038575 56168624140574982859557863)
    ·
      refine ⟨84252936210862474289336795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56168624140574982859557863 84252936210862474289336795)
      ·
        refine ⟨126379404316293711434005193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84252936210862474289336795 126379404316293711434005193)
        ·
          refine ⟨94784553237220283575503895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126379404316293711434005193 94784553237220283575503895)
          ·
            refine ⟨142176829855830425363255843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94784553237220283575503895 142176829855830425363255843)
            ·
              refine ⟨213265244783745638044883765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142176829855830425363255843 213265244783745638044883765)
              ·
                refine ⟨19993616698476153566707853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213265244783745638044883765 19993616698476153566707853)
                ·
                  refine ⟨7497606261928557587515445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19993616698476153566707853 7497606261928557587515445)
                  ·
                    refine ⟨702900587055802273829573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7497606261928557587515445 702900587055802273829573)
                    ·
                      rfl

theorem cell23_4106682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_4106682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106682 prefixEnd_4106682 := by exact prefixLift 4106682
  have htrace : WordTrace (prefixWord ++ tailWord_4106682) baseStart_4106682 baseEnd_4106682 := by
    simpa [prefixWord, tailWord_4106682, baseEnd_4106682] using wordTrace_append hprefix tailTrace_4106682
  have hstable : (prefixWord ++ tailWord_4106682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106682).length < 2 ^ (prefixWord ++ tailWord_4106682).sum := by decide
  have hdescent : baseEnd_4106682 < baseStart_4106682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106732 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_4106732 : Nat := 118140960795 + 4106732 * 2 ^ 59
def prefixEnd_4106732 : Nat := 4983230072969 + 3 ^ 40 * 4106732 * 2
def baseEnd_4106732 : Nat := 2108727435200131625863489

theorem tailTrace_4106732 : CollatzResearch.WordTrace tailWord_4106732 prefixEnd_4106732 2108727435200131625863489 := by
  unfold tailWord_4106732
  simp only [CollatzResearch.WordTrace]
  refine ⟨74892410679009406415737225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99856547572012541887649633 74892410679009406415737225)
  ·
    refine ⟨56169308009257054811802919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74892410679009406415737225 56169308009257054811802919)
    ·
      refine ⟨84253962013885582217704379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56169308009257054811802919 84253962013885582217704379)
      ·
        refine ⟨126380943020828373326556569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84253962013885582217704379 126380943020828373326556569)
        ·
          refine ⟨94785707265621279994917427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126380943020828373326556569 94785707265621279994917427)
          ·
            refine ⟨142178560898431919992376141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94785707265621279994917427 142178560898431919992376141)
            ·
              refine ⟨53316960336911969997141053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142178560898431919992376141 53316960336911969997141053)
              ·
                refine ⟨19993860126341988748927895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53316960336911969997141053 19993860126341988748927895)
                ·
                  refine ⟨29990790189512983123391843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19993860126341988748927895 29990790189512983123391843)
                  ·
                    refine ⟨44986185284269474685087765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29990790189512983123391843 44986185284269474685087765)
                    ·
                      refine ⟨2108727435200131625863489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44986185284269474685087765 2108727435200131625863489)
                      ·
                        rfl

theorem cell23_4106732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_4106732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106732 prefixEnd_4106732 := by exact prefixLift 4106732
  have htrace : WordTrace (prefixWord ++ tailWord_4106732) baseStart_4106732 baseEnd_4106732 := by
    simpa [prefixWord, tailWord_4106732, baseEnd_4106732] using wordTrace_append hprefix tailTrace_4106732
  have hstable : (prefixWord ++ tailWord_4106732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106732).length < 2 ^ (prefixWord ++ tailWord_4106732).sum := by decide
  have hdescent : baseEnd_4106732 < baseStart_4106732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106733 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_4106733 : Nat := 118140960795 + 4106733 * 2 ^ 59
def prefixEnd_4106733 : Nat := 4983230072969 + 3 ^ 40 * 4106733 * 2
def baseEnd_4106733 : Nat := 702909316226928707316995

theorem tailTrace_4106733 : CollatzResearch.WordTrace tailWord_4106733 prefixEnd_4106733 702909316226928707316995 := by
  unfold tailWord_4106733
  simp only [CollatzResearch.WordTrace]
  refine ⟨149784857831015190002260853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99856571887343460001507235 149784857831015190002260853)
  ·
    refine ⟨14042330421657674062711955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149784857831015190002260853 14042330421657674062711955)
    ·
      refine ⟨21063495632486511094067933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14042330421657674062711955 21063495632486511094067933)
      ·
        refine ⟨7898810862182441660275475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21063495632486511094067933 7898810862182441660275475)
        ·
          refine ⟨11848216293273662490413213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898810862182441660275475 11848216293273662490413213)
          ·
            refine ⟨4443081109977623433904955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11848216293273662490413213 4443081109977623433904955)
            ·
              refine ⟨6664621664966435150857433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443081109977623433904955 6664621664966435150857433)
              ·
                refine ⟨4998466248724826363143075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6664621664966435150857433 4998466248724826363143075)
                ·
                  refine ⟨7497699373087239544714613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998466248724826363143075 7497699373087239544714613)
                  ·
                    refine ⟨702909316226928707316995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7497699373087239544714613 702909316226928707316995)
                    ·
                      rfl

theorem cell23_4106733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_4106733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106733 prefixEnd_4106733 := by exact prefixLift 4106733
  have htrace : WordTrace (prefixWord ++ tailWord_4106733) baseStart_4106733 baseEnd_4106733 := by
    simpa [prefixWord, tailWord_4106733, baseEnd_4106733] using wordTrace_append hprefix tailTrace_4106733
  have hstable : (prefixWord ++ tailWord_4106733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106733).length < 2 ^ (prefixWord ++ tailWord_4106733).sum := by decide
  have hdescent : baseEnd_4106733 < baseStart_4106733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106736 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 5, 2, 2]
def baseStart_4106736 : Nat := 118140960795 + 4106736 * 2 ^ 59
def prefixEnd_4106736 : Nat := 4983230072969 + 3 ^ 40 * 4106736 * 2
def baseEnd_4106736 : Nat := 2108729489122749610213471

theorem tailTrace_4106736 : CollatzResearch.WordTrace tailWord_4106736 prefixEnd_4106736 2108729489122749610213471 := by
  unfold tailWord_4106736
  simp only [CollatzResearch.WordTrace]
  refine ⟨74892483625002160757310031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99856644833336214343080041 74892483625002160757310031)
  ·
    refine ⟨112338725437503241135965047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74892483625002160757310031 112338725437503241135965047)
    ·
      refine ⟨168508088156254861703947571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112338725437503241135965047 168508088156254861703947571)
      ·
        refine ⟨252762132234382292555921357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168508088156254861703947571 252762132234382292555921357)
        ·
          refine ⟨94785799587893359708470509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252762132234382292555921357 94785799587893359708470509)
          ·
            refine ⟨35544674845460009890676441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94785799587893359708470509 35544674845460009890676441)
            ·
              refine ⟨26658506134095007418007331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35544674845460009890676441 26658506134095007418007331)
              ·
                refine ⟨39987759201142511127010997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26658506134095007418007331 39987759201142511127010997)
                ·
                  refine ⟨3748852425107110418157281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39987759201142511127010997 3748852425107110418157281)
                  ·
                    refine ⟨2811639318830332813617961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3748852425107110418157281 2811639318830332813617961)
                    ·
                      refine ⟨2108729489122749610213471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811639318830332813617961 2108729489122749610213471)
                      ·
                        rfl

theorem cell23_4106736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 2, 2].length) (baseStart_4106736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106736 prefixEnd_4106736 := by exact prefixLift 4106736
  have htrace : WordTrace (prefixWord ++ tailWord_4106736) baseStart_4106736 baseEnd_4106736 := by
    simpa [prefixWord, tailWord_4106736, baseEnd_4106736] using wordTrace_append hprefix tailTrace_4106736
  have hstable : (prefixWord ++ tailWord_4106736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106736).length < 2 ^ (prefixWord ++ tailWord_4106736).sum := by decide
  have hdescent : baseEnd_4106736 < baseStart_4106736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106739 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 3]
def baseStart_4106739 : Nat := 118140960795 + 4106739 * 2 ^ 59
def prefixEnd_4106739 : Nat := 4983230072969 + 3 ^ 40 * 4106739 * 2
def baseEnd_4106739 : Nat := 2108731029564713098475957

theorem tailTrace_4106739 : CollatzResearch.WordTrace tailWord_4106739 prefixEnd_4106739 2108731029564713098475957 := by
  unfold tailWord_4106739
  simp only [CollatzResearch.WordTrace]
  refine ⟨149785076668993453026979271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99856717779328968684652847 149785076668993453026979271)
  ·
    refine ⟨224677615003490179540468907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149785076668993453026979271 224677615003490179540468907)
    ·
      refine ⟨337016422505235269310703361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224677615003490179540468907 337016422505235269310703361)
      ·
        refine ⟨252762316878926451983027521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337016422505235269310703361 252762316878926451983027521)
        ·
          refine ⟨189571737659194838987270641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252762316878926451983027521 189571737659194838987270641)
          ·
            refine ⟨142178803244396129240452981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189571737659194838987270641 142178803244396129240452981)
            ·
              refine ⟨13329262804162137116292467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142178803244396129240452981 13329262804162137116292467)
              ·
                refine ⟨19993894206243205674438701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13329262804162137116292467 19993894206243205674438701)
                ·
                  refine ⟨7497710327341202127914513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19993894206243205674438701 7497710327341202127914513)
                  ·
                    refine ⟨5623282745505901595935885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7497710327341202127914513 5623282745505901595935885)
                    ·
                      refine ⟨2108731029564713098475957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5623282745505901595935885 2108731029564713098475957)
                      ·
                        rfl

theorem cell23_4106739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_4106739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106739 prefixEnd_4106739 := by exact prefixLift 4106739
  have htrace : WordTrace (prefixWord ++ tailWord_4106739) baseStart_4106739 baseEnd_4106739 := by
    simpa [prefixWord, tailWord_4106739, baseEnd_4106739] using wordTrace_append hprefix tailTrace_4106739
  have hstable : (prefixWord ++ tailWord_4106739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106739).length < 2 ^ (prefixWord ++ tailWord_4106739).sum := by decide
  have hdescent : baseEnd_4106739 < baseStart_4106739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106749 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_4106749 : Nat := 118140960795 + 4106749 * 2 ^ 59
def prefixEnd_4106749 : Nat := 4983230072969 + 3 ^ 40 * 4106749 * 2
def baseEnd_4106749 : Nat := 2108736164371258059350911

theorem tailTrace_4106749 : CollatzResearch.WordTrace tailWord_4106749 prefixEnd_4106749 2108736164371258059350911 := by
  unfold tailWord_4106749
  simp only [CollatzResearch.WordTrace]
  refine ⟨149785441398957224734843301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99856960932638149823228867 149785441398957224734843301)
  ·
    refine ⟨28084770262304479637783119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149785441398957224734843301 28084770262304479637783119)
    ·
      refine ⟨42127155393456719456674679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28084770262304479637783119 42127155393456719456674679)
      ·
        refine ⟨63190733090185079185012019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42127155393456719456674679 63190733090185079185012019)
        ·
          refine ⟨94786099635277618777518029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63190733090185079185012019 94786099635277618777518029)
          ·
            refine ⟨35544787363229107041569261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94786099635277618777518029 35544787363229107041569261)
            ·
              refine ⟨13329295261210915140588473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35544787363229107041569261 13329295261210915140588473)
              ·
                refine ⟨9996971445908186355441355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13329295261210915140588473 9996971445908186355441355)
                ·
                  refine ⟨14995457168862279533162033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9996971445908186355441355 14995457168862279533162033)
                  ·
                    refine ⟨11246592876646709649871525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14995457168862279533162033 11246592876646709649871525)
                    ·
                      refine ⟨2108736164371258059350911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11246592876646709649871525 2108736164371258059350911)
                      ·
                        rfl

theorem cell23_4106749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_4106749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106749 prefixEnd_4106749 := by exact prefixLift 4106749
  have htrace : WordTrace (prefixWord ++ tailWord_4106749) baseStart_4106749 baseEnd_4106749 := by
    simpa [prefixWord, tailWord_4106749, baseEnd_4106749] using wordTrace_append hprefix tailTrace_4106749
  have hstable : (prefixWord ++ tailWord_4106749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106749).length < 2 ^ (prefixWord ++ tailWord_4106749).sum := by decide
  have hdescent : baseEnd_4106749 < baseStart_4106749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106753 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_4106753 : Nat := 118140960795 + 4106753 * 2 ^ 59
def prefixEnd_4106753 : Nat := 4983230072969 + 3 ^ 40 * 4106753 * 2
def baseEnd_4106753 : Nat := 2108738218293876043700893

theorem tailTrace_4106753 : CollatzResearch.WordTrace tailWord_4106753 prefixEnd_4106753 2108738218293876043700893 := by
  unfold tailWord_4106753
  simp only [CollatzResearch.WordTrace]
  refine ⟨149785587290942733417988913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99857058193961822278659275 149785587290942733417988913)
  ·
    refine ⟨112339190468207050063491685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149785587290942733417988913 112339190468207050063491685)
    ·
      refine ⟨21063598212788821886904691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112339190468207050063491685 21063598212788821886904691)
      ·
        refine ⟨31595397319183232830357037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21063598212788821886904691 31595397319183232830357037)
        ·
          refine ⟨11848273994693712311383889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31595397319183232830357037 11848273994693712311383889)
          ·
            refine ⟨8886205496020284233537917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11848273994693712311383889 8886205496020284233537917)
            ·
              refine ⟨3332327061007606587576719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8886205496020284233537917 3332327061007606587576719)
              ·
                refine ⟨4998490591511409881365079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332327061007606587576719 4998490591511409881365079)
                ·
                  refine ⟨7497735887267114822047619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998490591511409881365079 7497735887267114822047619)
                  ·
                    refine ⟨11246603830900672233071429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7497735887267114822047619 11246603830900672233071429)
                    ·
                      refine ⟨2108738218293876043700893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11246603830900672233071429 2108738218293876043700893)
                      ·
                        rfl

theorem cell23_4106753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_4106753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106753 prefixEnd_4106753 := by exact prefixLift 4106753
  have htrace : WordTrace (prefixWord ++ tailWord_4106753) baseStart_4106753 baseEnd_4106753 := by
    simpa [prefixWord, tailWord_4106753, baseEnd_4106753] using wordTrace_append hprefix tailTrace_4106753
  have hstable : (prefixWord ++ tailWord_4106753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106753).length < 2 ^ (prefixWord ++ tailWord_4106753).sum := by decide
  have hdescent : baseEnd_4106753 < baseStart_4106753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106756 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4106756 : Nat := 118140960795 + 4106756 * 2 ^ 59
def prefixEnd_4106756 : Nat := 4983230072969 + 3 ^ 40 * 4106756 * 2
def baseEnd_4106756 : Nat := 2108739758735839531963379

theorem tailTrace_4106756 : CollatzResearch.WordTrace tailWord_4106756 prefixEnd_4106756 2108739758735839531963379 := by
  unfold tailWord_4106756
  simp only [CollatzResearch.WordTrace]
  refine ⟨74892848354965932465174061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99857131139954576620232081 74892848354965932465174061)
  ·
    refine ⟨28084818133112224674440273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74892848354965932465174061 28084818133112224674440273)
    ·
      refine ⟨21063613599834168505830205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28084818133112224674440273 21063613599834168505830205)
      ·
        refine ⟨7898855099937813189686327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21063613599834168505830205 7898855099937813189686327)
        ·
          refine ⟨11848282649906719784529491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898855099937813189686327 11848282649906719784529491)
          ·
            refine ⟨17772423974860079676794237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11848282649906719784529491 17772423974860079676794237)
            ·
              refine ⟨6664658990572529878797839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17772423974860079676794237 6664658990572529878797839)
              ·
                refine ⟨9996988485858794818196759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664658990572529878797839 9996988485858794818196759)
                ·
                  refine ⟨14995482728788192227295139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9996988485858794818196759 14995482728788192227295139)
                  ·
                    refine ⟨22493224093182288340942709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14995482728788192227295139 22493224093182288340942709)
                    ·
                      refine ⟨2108739758735839531963379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22493224093182288340942709 2108739758735839531963379)
                      ·
                        rfl

theorem cell23_4106756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4106756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106756 prefixEnd_4106756 := by exact prefixLift 4106756
  have htrace : WordTrace (prefixWord ++ tailWord_4106756) baseStart_4106756 baseEnd_4106756 := by
    simpa [prefixWord, tailWord_4106756, baseEnd_4106756] using wordTrace_append hprefix tailTrace_4106756
  have hstable : (prefixWord ++ tailWord_4106756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106756).length < 2 ^ (prefixWord ++ tailWord_4106756).sum := by decide
  have hdescent : baseEnd_4106756 < baseStart_4106756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106759 : List Nat := [1, 1, 4, 3, 4, 10]
def baseStart_4106759 : Nat := 118140960795 + 4106759 * 2 ^ 59
def prefixEnd_4106759 : Nat := 4983230072969 + 3 ^ 40 * 4106759 * 2
def baseEnd_4106759 : Nat := 8677947733241987737555

theorem tailTrace_4106759 : CollatzResearch.WordTrace tailWord_4106759 prefixEnd_4106759 8677947733241987737555 := by
  unfold tailWord_4106759
  simp only [CollatzResearch.WordTrace]
  refine ⟨149785806128920996442707331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99857204085947330961804887 149785806128920996442707331)
  ·
    refine ⟨224678709193381494664060997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149785806128920996442707331 224678709193381494664060997)
    ·
      refine ⟨42127257973759030249511437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224678709193381494664060997 42127257973759030249511437)
      ·
        refine ⟨15797721740159636343566789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42127257973759030249511437 15797721740159636343566789)
        ·
          refine ⟨2962072826279931814418773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15797721740159636343566789 2962072826279931814418773)
          ·
            refine ⟨8677947733241987737555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2962072826279931814418773 8677947733241987737555)
            ·
              rfl

theorem cell23_4106759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 10].length) (baseStart_4106759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106759 prefixEnd_4106759 := by exact prefixLift 4106759
  have htrace : WordTrace (prefixWord ++ tailWord_4106759) baseStart_4106759 baseEnd_4106759 := by
    simpa [prefixWord, tailWord_4106759, baseEnd_4106759] using wordTrace_append hprefix tailTrace_4106759
  have hstable : (prefixWord ++ tailWord_4106759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106759).length < 2 ^ (prefixWord ++ tailWord_4106759).sum := by decide
  have hdescent : baseEnd_4106759 < baseStart_4106759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106786 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_4106786 : Nat := 118140960795 + 4106786 * 2 ^ 59
def prefixEnd_4106786 : Nat := 4983230072969 + 3 ^ 40 * 4106786 * 2
def baseEnd_4106786 : Nat := 2108755163155474414588241

theorem tailTrace_4106786 : CollatzResearch.WordTrace tailWord_4106786 prefixEnd_4106786 2108755163155474414588241 := by
  unfold tailWord_4106786
  simp only [CollatzResearch.WordTrace]
  refine ⟨37446697724955795013485053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99857860599882120035960141 37446697724955795013485053)
  ·
    refine ⟨14042511646858423130056895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37446697724955795013485053 14042511646858423130056895)
    ·
      refine ⟨21063767470287634695085343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14042511646858423130056895 21063767470287634695085343)
      ·
        refine ⟨31595651205431452042628015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21063767470287634695085343 31595651205431452042628015)
        ·
          refine ⟨47393476808147178063942023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31595651205431452042628015 47393476808147178063942023)
          ·
            refine ⟨71090215212220767095913035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47393476808147178063942023 71090215212220767095913035)
            ·
              refine ⟨106635322818331150643869553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71090215212220767095913035 106635322818331150643869553)
              ·
                refine ⟨79976492113748362982902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106635322818331150643869553 79976492113748362982902165)
                ·
                  refine ⟨3748898067831954514823539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79976492113748362982902165 3748898067831954514823539)
                  ·
                    refine ⟨5623347101747931772235309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3748898067831954514823539 5623347101747931772235309)
                    ·
                      refine ⟨2108755163155474414588241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5623347101747931772235309 2108755163155474414588241)
                      ·
                        rfl

theorem cell23_4106786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_4106786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106786 prefixEnd_4106786 := by exact prefixLift 4106786
  have htrace : WordTrace (prefixWord ++ tailWord_4106786) baseStart_4106786 baseEnd_4106786 := by
    simpa [prefixWord, tailWord_4106786, baseEnd_4106786] using wordTrace_append hprefix tailTrace_4106786
  have hstable : (prefixWord ++ tailWord_4106786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106786).length < 2 ^ (prefixWord ++ tailWord_4106786).sum := by decide
  have hdescent : baseEnd_4106786 < baseStart_4106786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106804 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4106804 : Nat := 118140960795 + 4106804 * 2 ^ 59
def prefixEnd_4106804 : Nat := 4983230072969 + 3 ^ 40 * 4106804 * 2
def baseEnd_4106804 : Nat := 2108764405807255344163159

theorem tailTrace_4106804 : CollatzResearch.WordTrace tailWord_4106804 prefixEnd_4106804 2108764405807255344163159 := by
  unfold tailWord_4106804
  simp only [CollatzResearch.WordTrace]
  refine ⟨74893723706878984564047733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99858298275838646085396977 74893723706878984564047733)
  ·
    refine ⟨7021286597519904802879475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74893723706878984564047733 7021286597519904802879475)
    ·
      refine ⟨10531929896279857204319213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7021286597519904802879475 10531929896279857204319213)
      ·
        refine ⟨3949473711104946451619705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10531929896279857204319213 3949473711104946451619705)
        ·
          refine ⟨2962105283328709838714779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3949473711104946451619705 2962105283328709838714779)
          ·
            refine ⟨4443157924993064758072169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962105283328709838714779 4443157924993064758072169)
            ·
              refine ⟨3332368443744798568554127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443157924993064758072169 3332368443744798568554127)
              ·
                refine ⟨4998552665617197852831191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332368443744798568554127 4998552665617197852831191)
                ·
                  refine ⟨7497828998425796779246787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998552665617197852831191 7497828998425796779246787)
                  ·
                    refine ⟨11246743497638695168870181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7497828998425796779246787 11246743497638695168870181)
                    ·
                      refine ⟨2108764405807255344163159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11246743497638695168870181 2108764405807255344163159)
                      ·
                        rfl

theorem cell23_4106804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4106804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106804 prefixEnd_4106804 := by exact prefixLift 4106804
  have htrace : WordTrace (prefixWord ++ tailWord_4106804) baseStart_4106804 baseEnd_4106804 := by
    simpa [prefixWord, tailWord_4106804, baseEnd_4106804] using wordTrace_append hprefix tailTrace_4106804
  have hstable : (prefixWord ++ tailWord_4106804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106804).length < 2 ^ (prefixWord ++ tailWord_4106804).sum := by decide
  have hdescent : baseEnd_4106804 < baseStart_4106804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106839 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_4106839 : Nat := 118140960795 + 4106839 * 2 ^ 59
def prefixEnd_4106839 : Nat := 4983230072969 + 3 ^ 40 * 4106839 * 2
def baseEnd_4106839 : Nat := 2108782377630162707225497

theorem tailTrace_4106839 : CollatzResearch.WordTrace tailWord_4106839 prefixEnd_4106839 2108782377630162707225497 := by
  unfold tailWord_4106839
  simp only [CollatzResearch.WordTrace]
  refine ⟨149788723968631170105619571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99859149312420780070413047 149788723968631170105619571)
  ·
    refine ⟨224683085952946755158429357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149788723968631170105619571 224683085952946755158429357)
    ·
      refine ⟨84256157232355033184411009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224683085952946755158429357 84256157232355033184411009)
      ·
        refine ⟨63192117924266274888308257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84256157232355033184411009 63192117924266274888308257)
        ·
          refine ⟨47394088443199706166231193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63192117924266274888308257 47394088443199706166231193)
          ·
            refine ⟨35545566332399779624673395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47394088443199706166231193 35545566332399779624673395)
            ·
              refine ⟨53318349498599669437010093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35545566332399779624673395 53318349498599669437010093)
              ·
                refine ⟨19994381061974876038878785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53318349498599669437010093 19994381061974876038878785)
                ·
                  refine ⟨14995785796481157029159089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19994381061974876038878785 14995785796481157029159089)
                  ·
                    refine ⟨11246839347360867771869317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14995785796481157029159089 11246839347360867771869317)
                    ·
                      refine ⟨2108782377630162707225497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11246839347360867771869317 2108782377630162707225497)
                      ·
                        rfl

theorem cell23_4106839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_4106839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106839 prefixEnd_4106839 := by exact prefixLift 4106839
  have htrace : WordTrace (prefixWord ++ tailWord_4106839) baseStart_4106839 baseEnd_4106839 := by
    simpa [prefixWord, tailWord_4106839, baseEnd_4106839] using wordTrace_append hprefix tailTrace_4106839
  have hstable : (prefixWord ++ tailWord_4106839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106839).length < 2 ^ (prefixWord ++ tailWord_4106839).sum := by decide
  have hdescent : baseEnd_4106839 < baseStart_4106839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106849 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 7]
def baseStart_4106849 : Nat := 118140960795 + 4106849 * 2 ^ 59
def prefixEnd_4106849 : Nat := 4983230072969 + 3 ^ 40 * 4106849 * 2
def baseEnd_4106849 : Nat := 234309723604078629788939

theorem tailTrace_4106849 : CollatzResearch.WordTrace tailWord_4106849 prefixEnd_4106849 234309723604078629788939 := by
  unfold tailWord_4106849
  simp only [CollatzResearch.WordTrace]
  refine ⟨149789088698594941813483601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99859392465729961208989067 149789088698594941813483601)
  ·
    refine ⟨112341816523946206360112701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149789088698594941813483601 112341816523946206360112701)
    ·
      refine ⟨42128181196479827385042263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112341816523946206360112701 42128181196479827385042263)
      ·
        refine ⟨63192271794719741077563395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42128181196479827385042263 63192271794719741077563395)
        ·
          refine ⟨94788407692079611616345093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63192271794719741077563395 94788407692079611616345093)
          ·
            refine ⟨17772826442264927178064705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94788407692079611616345093 17772826442264927178064705)
            ·
              refine ⟨13329619831698695383548529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17772826442264927178064705 13329619831698695383548529)
              ·
                refine ⟨9997214873774021537661397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13329619831698695383548529 9997214873774021537661397)
                ·
                  refine ⟨234309723604078629788939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9997214873774021537661397 234309723604078629788939)
                  ·
                    rfl

theorem cell23_4106849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 7].length) (baseStart_4106849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106849 prefixEnd_4106849 := by exact prefixLift 4106849
  have htrace : WordTrace (prefixWord ++ tailWord_4106849) baseStart_4106849 baseEnd_4106849 := by
    simpa [prefixWord, tailWord_4106849, baseEnd_4106849] using wordTrace_append hprefix tailTrace_4106849
  have hstable : (prefixWord ++ tailWord_4106849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106849).length < 2 ^ (prefixWord ++ tailWord_4106849).sum := by decide
  have hdescent : baseEnd_4106849 < baseStart_4106849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106859 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 3]
def baseStart_4106859 : Nat := 118140960795 + 4106859 * 2 ^ 59
def prefixEnd_4106859 : Nat := 4983230072969 + 3 ^ 40 * 4106859 * 2
def baseEnd_4106859 : Nat := 2108792647243252628975405

theorem tailTrace_4106859 : CollatzResearch.WordTrace tailWord_4106859 prefixEnd_4106859 2108792647243252628975405 := by
  unfold tailWord_4106859
  simp only [CollatzResearch.WordTrace]
  refine ⟨149789453428558713521347631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99859635619039142347565087 149789453428558713521347631)
  ·
    refine ⟨224684180142838070282021447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149789453428558713521347631 224684180142838070282021447)
    ·
      refine ⟨337026270214257105423032171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224684180142838070282021447 337026270214257105423032171)
      ·
        refine ⟨505539405321385658134548257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337026270214257105423032171 505539405321385658134548257)
        ·
          refine ⟨379154553991039243600911193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505539405321385658134548257 379154553991039243600911193)
          ·
            refine ⟨284365915493279432700683395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379154553991039243600911193 284365915493279432700683395)
            ·
              refine ⟨426548873239919149051025093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284365915493279432700683395 426548873239919149051025093)
              ·
                refine ⟨79977913732484840447067205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426548873239919149051025093 79977913732484840447067205)
                ·
                  refine ⟨14995858824840907583825101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79977913732484840447067205 14995858824840907583825101)
                  ·
                    refine ⟨5623447059315340343934413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14995858824840907583825101 5623447059315340343934413)
                    ·
                      refine ⟨2108792647243252628975405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5623447059315340343934413 2108792647243252628975405)
                      ·
                        rfl

theorem cell23_4106859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 3].length) (baseStart_4106859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106859 prefixEnd_4106859 := by exact prefixLift 4106859
  have htrace : WordTrace (prefixWord ++ tailWord_4106859) baseStart_4106859 baseEnd_4106859 := by
    simpa [prefixWord, tailWord_4106859, baseEnd_4106859] using wordTrace_append hprefix tailTrace_4106859
  have hstable : (prefixWord ++ tailWord_4106859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106859).length < 2 ^ (prefixWord ++ tailWord_4106859).sum := by decide
  have hdescent : baseEnd_4106859 < baseStart_4106859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106909 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_4106909 : Nat := 118140960795 + 4106909 * 2 ^ 59
def prefixEnd_4106909 : Nat := 4983230072969 + 3 ^ 40 * 4106909 * 2
def baseEnd_4106909 : Nat := 702939440425325811116725

theorem tailTrace_4106909 : CollatzResearch.WordTrace tailWord_4106909 prefixEnd_4106909 702939440425325811116725 := by
  unfold tailWord_4106909
  simp only [CollatzResearch.WordTrace]
  refine ⟨149791277078377572060667781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99860851385585048040445187 149791277078377572060667781)
  ·
    refine ⟨28085864452195794761375209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149791277078377572060667781 28085864452195794761375209)
    ·
      refine ⟨21064398339146846071031407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28085864452195794761375209 21064398339146846071031407)
      ·
        refine ⟨31596597508720269106547111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21064398339146846071031407 31596597508720269106547111)
        ·
          refine ⟨47394896263080403659820667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31596597508720269106547111 47394896263080403659820667)
          ·
            refine ⟨71092344394620605489731001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47394896263080403659820667 71092344394620605489731001)
            ·
              refine ⟨53319258295965454117298251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71092344394620605489731001 53319258295965454117298251)
              ·
                refine ⟨79978887443948181175947377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53319258295965454117298251 79978887443948181175947377)
                ·
                  refine ⟨59984165582961135881960533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79978887443948181175947377 59984165582961135881960533)
                  ·
                    refine ⟨702939440425325811116725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59984165582961135881960533 702939440425325811116725)
                    ·
                      rfl

theorem cell23_4106909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_4106909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106909 prefixEnd_4106909 := by exact prefixLift 4106909
  have htrace : WordTrace (prefixWord ++ tailWord_4106909) baseStart_4106909 baseEnd_4106909 := by
    simpa [prefixWord, tailWord_4106909, baseEnd_4106909] using wordTrace_append hprefix tailTrace_4106909
  have hstable : (prefixWord ++ tailWord_4106909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106909).length < 2 ^ (prefixWord ++ tailWord_4106909).sum := by decide
  have hdescent : baseEnd_4106909 < baseStart_4106909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106913 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 2, 5]
def baseStart_4106913 : Nat := 118140960795 + 4106913 * 2 ^ 59
def prefixEnd_4106913 : Nat := 4983230072969 + 3 ^ 40 * 4106913 * 2
def baseEnd_4106913 : Nat := 702940125066198472566719

theorem tailTrace_4106913 : CollatzResearch.WordTrace tailWord_4106913 prefixEnd_4106913 702940125066198472566719 := by
  unfold tailWord_4106913
  simp only [CollatzResearch.WordTrace]
  refine ⟨149791422970363080743813393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99860948646908720495875595 149791422970363080743813393)
  ·
    refine ⟨112343567227772310557860045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149791422970363080743813393 112343567227772310557860045)
    ·
      refine ⟨42128837710414616459197517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112343567227772310557860045 42128837710414616459197517)
      ·
        refine ⟨15798314141405481172199069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42128837710414616459197517 15798314141405481172199069)
        ·
          refine ⟨5924367803027055439574651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15798314141405481172199069 5924367803027055439574651)
          ·
            refine ⟨8886551704540583159361977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924367803027055439574651 8886551704540583159361977)
            ·
              refine ⟨6664913778405437369521483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8886551704540583159361977 6664913778405437369521483)
              ·
                refine ⟨9997370667608156054282225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664913778405437369521483 9997370667608156054282225)
                ·
                  refine ⟨7498028000706117040711669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9997370667608156054282225 7498028000706117040711669)
                  ·
                    refine ⟨702940125066198472566719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7498028000706117040711669 702940125066198472566719)
                    ·
                      rfl

theorem cell23_4106913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_4106913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106913 prefixEnd_4106913 := by exact prefixLift 4106913
  have htrace : WordTrace (prefixWord ++ tailWord_4106913) baseStart_4106913 baseEnd_4106913 := by
    simpa [prefixWord, tailWord_4106913, baseEnd_4106913] using wordTrace_append hprefix tailTrace_4106913
  have hstable : (prefixWord ++ tailWord_4106913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106913).length < 2 ^ (prefixWord ++ tailWord_4106913).sum := by decide
  have hdescent : baseEnd_4106913 < baseStart_4106913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106933 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4106933 : Nat := 118140960795 + 4106933 * 2 ^ 59
def prefixEnd_4106933 : Nat := 4983230072969 + 3 ^ 40 * 4106933 * 2
def baseEnd_4106933 : Nat := 2108830644811685339450065

theorem tailTrace_4106933 : CollatzResearch.WordTrace tailWord_4106933 prefixEnd_4106933 2108830644811685339450065 := by
  unfold tailWord_4106933
  simp only [CollatzResearch.WordTrace]
  refine ⟨149792152430290624159541453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99861434953527082773027635 149792152430290624159541453)
  ·
    refine ⟨56172057161358984059828045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149792152430290624159541453 56172057161358984059828045)
    ·
      refine ⟨21064521435509619022435517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56172057161358984059828045 21064521435509619022435517)
      ·
        refine ⟨7899195538316107133413319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21064521435509619022435517 7899195538316107133413319)
        ·
          refine ⟨11848793307474160700119979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7899195538316107133413319 11848793307474160700119979)
          ·
            refine ⟨17773189961211241050179969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11848793307474160700119979 17773189961211241050179969)
            ·
              refine ⟨13329892470908430787634977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17773189961211241050179969 13329892470908430787634977)
              ·
                refine ⟨9997419353181323090726233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13329892470908430787634977 9997419353181323090726233)
                ·
                  refine ⟨7498064514885992318044675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9997419353181323090726233 7498064514885992318044675)
                  ·
                    refine ⟨11247096772328988477067013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7498064514885992318044675 11247096772328988477067013)
                    ·
                      refine ⟨2108830644811685339450065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11247096772328988477067013 2108830644811685339450065)
                      ·
                        rfl

theorem cell23_4106933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4106933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106933 prefixEnd_4106933 := by exact prefixLift 4106933
  have htrace : WordTrace (prefixWord ++ tailWord_4106933) baseStart_4106933 baseEnd_4106933 := by
    simpa [prefixWord, tailWord_4106933, baseEnd_4106933] using wordTrace_append hprefix tailTrace_4106933
  have hstable : (prefixWord ++ tailWord_4106933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106933).length < 2 ^ (prefixWord ++ tailWord_4106933).sum := by decide
  have hdescent : baseEnd_4106933 < baseStart_4106933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106934 : List Nat := [5, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_4106934 : Nat := 118140960795 + 4106934 * 2 ^ 59
def prefixEnd_4106934 : Nat := 4983230072969 + 3 ^ 40 * 4106934 * 2
def baseEnd_4106934 : Nat := 234314573143593315059729

theorem tailTrace_4106934 : CollatzResearch.WordTrace tailWord_4106934 prefixEnd_4106934 234314573143593315059729 := by
  unfold tailWord_4106934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362011806455437583145491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99861459268858000886885237 9362011806455437583145491)
  ·
    refine ⟨14043017709683156374718237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9362011806455437583145491 14043017709683156374718237)
    ·
      refine ⟨5266131641131183640519339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14043017709683156374718237 5266131641131183640519339)
      ·
        refine ⟨7899197461696775460779009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266131641131183640519339 7899197461696775460779009)
        ·
          refine ⟨5924398096272581595584257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7899197461696775460779009 5924398096272581595584257)
          ·
            refine ⟨4443298572204436196688193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5924398096272581595584257 4443298572204436196688193)
            ·
              refine ⟨3332473929153327147516145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443298572204436196688193 3332473929153327147516145)
              ·
                refine ⟨2499355446864995360637109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3332473929153327147516145 2499355446864995360637109)
                ·
                  refine ⟨234314573143593315059729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2499355446864995360637109 234314573143593315059729)
                  ·
                    rfl

theorem cell23_4106934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_4106934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106934 prefixEnd_4106934 := by exact prefixLift 4106934
  have htrace : WordTrace (prefixWord ++ tailWord_4106934) baseStart_4106934 baseEnd_4106934 := by
    simpa [prefixWord, tailWord_4106934, baseEnd_4106934] using wordTrace_append hprefix tailTrace_4106934
  have hstable : (prefixWord ++ tailWord_4106934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106934).length < 2 ^ (prefixWord ++ tailWord_4106934).sum := by decide
  have hdescent : baseEnd_4106934 < baseStart_4106934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106993 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 4, 3, 2]
def baseStart_4106993 : Nat := 118140960795 + 4106993 * 2 ^ 59
def prefixEnd_4106993 : Nat := 4983230072969 + 3 ^ 40 * 4106993 * 2
def baseEnd_4106993 : Nat := 2108861453650955104699789

theorem tailTrace_4106993 : CollatzResearch.WordTrace tailWord_4106993 prefixEnd_4106993 2108861453650955104699789 := by
  unfold tailWord_4106993
  simp only [CollatzResearch.WordTrace]
  refine ⟨149794340810073254406725633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99862893873382169604483755 149794340810073254406725633)
  ·
    refine ⟨112345755607554940805044225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149794340810073254406725633 112345755607554940805044225)
    ·
      refine ⟨84259316705666205603783169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112345755607554940805044225 84259316705666205603783169)
      ·
        refine ⟨63194487529249654202837377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84259316705666205603783169 63194487529249654202837377)
        ·
          refine ⟨47395865646937240652128033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63194487529249654202837377 47395865646937240652128033)
          ·
            refine ⟨35546899235202930489096025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47395865646937240652128033 35546899235202930489096025)
            ·
              refine ⟨26660174426402197866822019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35546899235202930489096025 26660174426402197866822019)
              ·
                refine ⟨39990261639603296800233029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26660174426402197866822019 39990261639603296800233029)
                ·
                  refine ⟨7498174057425618150043693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39990261639603296800233029 7498174057425618150043693)
                  ·
                    refine ⟨2811815271534606806266385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7498174057425618150043693 2811815271534606806266385)
                    ·
                      refine ⟨2108861453650955104699789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811815271534606806266385 2108861453650955104699789)
                      ·
                        rfl

theorem cell23_4106993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_4106993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4106993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4106993 prefixEnd_4106993 := by exact prefixLift 4106993
  have htrace : WordTrace (prefixWord ++ tailWord_4106993) baseStart_4106993 baseEnd_4106993 := by
    simpa [prefixWord, tailWord_4106993, baseEnd_4106993] using wordTrace_append hprefix tailTrace_4106993
  have hstable : (prefixWord ++ tailWord_4106993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106993).length < 2 ^ (prefixWord ++ tailWord_4106993).sum := by decide
  have hdescent : baseEnd_4106993 < baseStart_4106993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107000 : List Nat := [2, 1, 2, 1, 1, 2, 3, 6, 1, 1, 3]
def baseStart_4107000 : Nat := 118140960795 + 4107000 * 2 ^ 59
def prefixEnd_4107000 : Nat := 4983230072969 + 3 ^ 40 * 4107000 * 2
def baseEnd_4107000 : Nat := 2108865048015536577312257

theorem tailTrace_4107000 : CollatzResearch.WordTrace tailWord_4107000 prefixEnd_4107000 2108865048015536577312257 := by
  unfold tailWord_4107000
  simp only [CollatzResearch.WordTrace]
  refine ⟨74897298060523947301115227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99863064080698596401486969 74897298060523947301115227)
  ·
    refine ⟨112345947090785920951672841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74897298060523947301115227 112345947090785920951672841)
    ·
      refine ⟨84259460318089440713754631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112345947090785920951672841 84259460318089440713754631)
      ·
        refine ⟨126389190477134161070631947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84259460318089440713754631 126389190477134161070631947)
        ·
          refine ⟨189583785715701241605947921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126389190477134161070631947 189583785715701241605947921)
          ·
            refine ⟨142187839286775931204460941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189583785715701241605947921 142187839286775931204460941)
            ·
              refine ⟨53320439732540974201672853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142187839286775931204460941 53320439732540974201672853)
              ·
                refine ⟨2499395612462858165703415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53320439732540974201672853 2499395612462858165703415)
                ·
                  refine ⟨3749093418694287248555123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499395612462858165703415 3749093418694287248555123)
                  ·
                    refine ⟨5623640128041430872832685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3749093418694287248555123 5623640128041430872832685)
                    ·
                      refine ⟨2108865048015536577312257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5623640128041430872832685 2108865048015536577312257)
                      ·
                        rfl

theorem cell23_4107000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 1, 3].length) (baseStart_4107000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107000 prefixEnd_4107000 := by exact prefixLift 4107000
  have htrace : WordTrace (prefixWord ++ tailWord_4107000) baseStart_4107000 baseEnd_4107000 := by
    simpa [prefixWord, tailWord_4107000, baseEnd_4107000] using wordTrace_append hprefix tailTrace_4107000
  have hstable : (prefixWord ++ tailWord_4107000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107000).length < 2 ^ (prefixWord ++ tailWord_4107000).sum := by decide
  have hdescent : baseEnd_4107000 < baseStart_4107000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107010 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_4107010 : Nat := 118140960795 + 4107010 * 2 ^ 59
def prefixEnd_4107010 : Nat := 4983230072969 + 3 ^ 40 * 4107010 * 2
def baseEnd_4107010 : Nat := 2108870182822081538187211

theorem tailTrace_4107010 : CollatzResearch.WordTrace tailWord_4107010 prefixEnd_4107010 2108870182822081538187211 := by
  unfold tailWord_4107010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37448740212752916577523621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99863307234007777540062989 37448740212752916577523621)
  ·
    refine ⟨7021638789891171858285679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37448740212752916577523621 7021638789891171858285679)
    ·
      refine ⟨10532458184836757787428519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7021638789891171858285679 10532458184836757787428519)
      ·
        refine ⟨15798687277255136681142779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10532458184836757787428519 15798687277255136681142779)
        ·
          refine ⟨23698030915882705021714169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15798687277255136681142779 23698030915882705021714169)
          ·
            refine ⟨17773523186912028766285627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23698030915882705021714169 17773523186912028766285627)
            ·
              refine ⟨26660284780368043149428441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17773523186912028766285627 26660284780368043149428441)
              ·
                refine ⟨19995213585276032362071331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26660284780368043149428441 19995213585276032362071331)
                ·
                  refine ⟨29992820377914048543106997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19995213585276032362071331 29992820377914048543106997)
                  ·
                    refine ⟨2811826910429442050916281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29992820377914048543106997 2811826910429442050916281)
                    ·
                      refine ⟨2108870182822081538187211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811826910429442050916281 2108870182822081538187211)
                      ·
                        rfl

theorem cell23_4107010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_4107010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107010 prefixEnd_4107010 := by exact prefixLift 4107010
  have htrace : WordTrace (prefixWord ++ tailWord_4107010) baseStart_4107010 baseEnd_4107010 := by
    simpa [prefixWord, tailWord_4107010, baseEnd_4107010] using wordTrace_append hprefix tailTrace_4107010
  have hstable : (prefixWord ++ tailWord_4107010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107010).length < 2 ^ (prefixWord ++ tailWord_4107010).sum := by decide
  have hdescent : baseEnd_4107010 < baseStart_4107010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107023 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 4]
def baseStart_4107023 : Nat := 118140960795 + 4107023 * 2 ^ 59
def prefixEnd_4107023 : Nat := 4983230072969 + 3 ^ 40 * 4107023 * 2
def baseEnd_4107023 : Nat := 2108876858070589987324651

theorem tailTrace_4107023 : CollatzResearch.WordTrace tailWord_4107023 prefixEnd_4107023 2108876858070589987324651 := by
  unfold tailWord_4107023
  simp only [CollatzResearch.WordTrace]
  refine ⟨149795434999964569530317723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99863623333309713020211815 149795434999964569530317723)
  ·
    refine ⟨224693152499946854295476585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149795434999964569530317723 224693152499946854295476585)
    ·
      refine ⟨168519864374960140721607439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224693152499946854295476585 168519864374960140721607439)
      ·
        refine ⟨252779796562440211082411159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168519864374960140721607439 252779796562440211082411159)
        ·
          refine ⟨379169694843660316623616739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252779796562440211082411159 379169694843660316623616739)
          ·
            refine ⟨568754542265490474935425109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379169694843660316623616739 568754542265490474935425109)
            ·
              refine ⟨6665092292173716503149513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 568754542265490474935425109 6665092292173716503149513)
              ·
                refine ⟨4998819219130287377362135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6665092292173716503149513 4998819219130287377362135)
                ·
                  refine ⟨7498228828695431066043203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998819219130287377362135 7498228828695431066043203)
                  ·
                    refine ⟨11247343243043146599064805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7498228828695431066043203 11247343243043146599064805)
                    ·
                      refine ⟨2108876858070589987324651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11247343243043146599064805 2108876858070589987324651)
                      ·
                        rfl

theorem cell23_4107023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 4].length) (baseStart_4107023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107023 prefixEnd_4107023 := by exact prefixLift 4107023
  have htrace : WordTrace (prefixWord ++ tailWord_4107023) baseStart_4107023 baseEnd_4107023 := by
    simpa [prefixWord, tailWord_4107023, baseEnd_4107023] using wordTrace_append hprefix tailTrace_4107023
  have hstable : (prefixWord ++ tailWord_4107023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107023).length < 2 ^ (prefixWord ++ tailWord_4107023).sum := by decide
  have hdescent : baseEnd_4107023 < baseStart_4107023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107086 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_4107086 : Nat := 118140960795 + 4107086 * 2 ^ 59
def prefixEnd_4107086 : Nat := 4983230072969 + 3 ^ 40 * 4107086 * 2
def baseEnd_4107086 : Nat := 2108909207351823240836861

theorem tailTrace_4107086 : CollatzResearch.WordTrace tailWord_4107086 prefixEnd_4107086 2108909207351823240836861 := by
  unfold tailWord_4107086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18724716599842041411232639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99865155199157554193240741 18724716599842041411232639)
  ·
    refine ⟨28087074899763062116848959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18724716599842041411232639 28087074899763062116848959)
    ·
      refine ⟨42130612349644593175273439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28087074899763062116848959 42130612349644593175273439)
      ·
        refine ⟨63195918524466889762910159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42130612349644593175273439 63195918524466889762910159)
        ·
          refine ⟨94793877786700334644365239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63195918524466889762910159 94793877786700334644365239)
          ·
            refine ⟨142190816680050501966547859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94793877786700334644365239 142190816680050501966547859)
            ·
              refine ⟨213286225020075752949821789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142190816680050501966547859 213286225020075752949821789)
              ·
                refine ⟨79982334382528407356183171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213286225020075752949821789 79982334382528407356183171)
                ·
                  refine ⟨119973501573792611034274757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79982334382528407356183171 119973501573792611034274757)
                  ·
                    refine ⟨22495031545086114568926517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119973501573792611034274757 22495031545086114568926517)
                    ·
                      refine ⟨2108909207351823240836861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22495031545086114568926517 2108909207351823240836861)
                      ·
                        rfl

theorem cell23_4107086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_4107086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107086 prefixEnd_4107086 := by exact prefixLift 4107086
  have htrace : WordTrace (prefixWord ++ tailWord_4107086) baseStart_4107086 baseEnd_4107086 := by
    simpa [prefixWord, tailWord_4107086, baseEnd_4107086] using wordTrace_append hprefix tailTrace_4107086
  have hstable : (prefixWord ++ tailWord_4107086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107086).length < 2 ^ (prefixWord ++ tailWord_4107086).sum := by decide
  have hdescent : baseEnd_4107086 < baseStart_4107086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107096 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_4107096 : Nat := 118140960795 + 4107096 * 2 ^ 59
def prefixEnd_4107096 : Nat := 4983230072969 + 3 ^ 40 * 4107096 * 2
def baseEnd_4107096 : Nat := 2108914342158368201711815

theorem tailTrace_4107096 : CollatzResearch.WordTrace tailWord_4107096 prefixEnd_4107096 2108914342158368201711815 := by
  unfold tailWord_4107096
  simp only [CollatzResearch.WordTrace]
  refine ⟨74899048764350051498862571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99865398352466735331816761 74899048764350051498862571)
  ·
    refine ⟨112348573146525077248293857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74899048764350051498862571 112348573146525077248293857)
    ·
      refine ⟨84261429859893807936220393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112348573146525077248293857 84261429859893807936220393)
      ·
        refine ⟨63196072394920355952165295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84261429859893807936220393 63196072394920355952165295)
        ·
          refine ⟨94794108592380533928247943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63196072394920355952165295 94794108592380533928247943)
          ·
            refine ⟨142191162888570800892371915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94794108592380533928247943 142191162888570800892371915)
            ·
              refine ⟨213286744332856201338557873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142191162888570800892371915 213286744332856201338557873)
              ·
                refine ⟨159965058249642151003918405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213286744332856201338557873 159965058249642151003918405)
                ·
                  refine ⟨29993448421807903313234701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159965058249642151003918405 29993448421807903313234701)
                  ·
                    refine ⟨11247543158177963742463013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29993448421807903313234701 11247543158177963742463013)
                    ·
                      refine ⟨2108914342158368201711815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11247543158177963742463013 2108914342158368201711815)
                      ·
                        rfl

theorem cell23_4107096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_4107096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107096 prefixEnd_4107096 := by exact prefixLift 4107096
  have htrace : WordTrace (prefixWord ++ tailWord_4107096) baseStart_4107096 baseEnd_4107096 := by
    simpa [prefixWord, tailWord_4107096, baseEnd_4107096] using wordTrace_append hprefix tailTrace_4107096
  have hstable : (prefixWord ++ tailWord_4107096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107096).length < 2 ^ (prefixWord ++ tailWord_4107096).sum := by decide
  have hdescent : baseEnd_4107096 < baseStart_4107096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107107 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 3]
def baseStart_4107107 : Nat := 118140960795 + 4107107 * 2 ^ 59
def prefixEnd_4107107 : Nat := 4983230072969 + 3 ^ 40 * 4107107 * 2
def baseEnd_4107107 : Nat := 2108919990445567658674265

theorem tailTrace_4107107 : CollatzResearch.WordTrace tailWord_4107107 prefixEnd_4107107 2108919990445567658674265 := by
  unfold tailWord_4107107
  simp only [CollatzResearch.WordTrace]
  refine ⟨149798498731660251876375575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99865665821106834584250383 149798498731660251876375575)
  ·
    refine ⟨224697748097490377814563363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149798498731660251876375575 224697748097490377814563363)
    ·
      refine ⟨337046622146235566721845045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224697748097490377814563363 337046622146235566721845045)
      ·
        refine ⟨31598120826209584380172973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337046622146235566721845045 31598120826209584380172973)
        ·
          refine ⟨11849295309828594142564865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31598120826209584380172973 11849295309828594142564865)
          ·
            refine ⟨8886971482371445606923649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11849295309828594142564865 8886971482371445606923649)
            ·
              refine ⟨6665228611778584205192737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8886971482371445606923649 6665228611778584205192737)
              ·
                refine ⟨4998921458833938153894553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6665228611778584205192737 4998921458833938153894553)
                ·
                  refine ⟨3749191094125453615420915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4998921458833938153894553 3749191094125453615420915)
                  ·
                    refine ⟨5623786641188180423131373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3749191094125453615420915 5623786641188180423131373)
                    ·
                      refine ⟨2108919990445567658674265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5623786641188180423131373 2108919990445567658674265)
                      ·
                        rfl

theorem cell23_4107107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_4107107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107107 prefixEnd_4107107 := by exact prefixLift 4107107
  have htrace : WordTrace (prefixWord ++ tailWord_4107107) baseStart_4107107 baseEnd_4107107 := by
    simpa [prefixWord, tailWord_4107107, baseEnd_4107107] using wordTrace_append hprefix tailTrace_4107107
  have hstable : (prefixWord ++ tailWord_4107107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107107).length < 2 ^ (prefixWord ++ tailWord_4107107).sum := by decide
  have hdescent : baseEnd_4107107 < baseStart_4107107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107130 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2]
def baseStart_4107130 : Nat := 118140960795 + 4107130 * 2 ^ 59
def prefixEnd_4107130 : Nat := 4983230072969 + 3 ^ 40 * 4107130 * 2
def baseEnd_4107130 : Nat := 2108931800500621068686659

theorem tailTrace_4107130 : CollatzResearch.WordTrace tailWord_4107130 prefixEnd_4107130 2108931800500621068686659 := by
  unfold tailWord_4107130
  simp only [CollatzResearch.WordTrace]
  refine ⟨37449834402644231701115711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99866225073717951202975229 37449834402644231701115711)
  ·
    refine ⟨56174751603966347551673567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37449834402644231701115711 56174751603966347551673567)
    ·
      refine ⟨84262127405949521327510351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56174751603966347551673567 84262127405949521327510351)
      ·
        refine ⟨126393191108924281991265527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84262127405949521327510351 126393191108924281991265527)
        ·
          refine ⟨189589786663386422986898291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126393191108924281991265527 189589786663386422986898291)
          ·
            refine ⟨284384679995079634480347437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189589786663386422986898291 284384679995079634480347437)
            ·
              refine ⟨106644254998154862930130289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284384679995079634480347437 106644254998154862930130289)
              ·
                refine ⟨79983191248616147197597717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106644254998154862930130289 79983191248616147197597717)
                ·
                  refine ⟨3749212089778881899887393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79983191248616147197597717 3749212089778881899887393)
                  ·
                    refine ⟨2811909067334161424915545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3749212089778881899887393 2811909067334161424915545)
                    ·
                      refine ⟨2108931800500621068686659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811909067334161424915545 2108931800500621068686659)
                      ·
                        rfl

theorem cell23_4107130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_4107130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107130 prefixEnd_4107130 := by exact prefixLift 4107130
  have htrace : WordTrace (prefixWord ++ tailWord_4107130) baseStart_4107130 baseEnd_4107130 := by
    simpa [prefixWord, tailWord_4107130, baseEnd_4107130] using wordTrace_append hprefix tailTrace_4107130
  have hstable : (prefixWord ++ tailWord_4107130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107130).length < 2 ^ (prefixWord ++ tailWord_4107130).sum := by decide
  have hdescent : baseEnd_4107130 < baseStart_4107130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107158 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4107158 : Nat := 118140960795 + 4107158 * 2 ^ 59
def prefixEnd_4107158 : Nat := 4983230072969 + 3 ^ 40 * 4107158 * 2
def baseEnd_4107158 : Nat := 2108946177958946959136531

theorem tailTrace_4107158 : CollatzResearch.WordTrace tailWord_4107158 prefixEnd_4107158 2108946177958946959136531 := by
  unfold tailWord_4107158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362522428404717974155133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99866905902983658390988085 9362522428404717974155133)
  ·
    refine ⟨3510945910651769240308175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9362522428404717974155133 3510945910651769240308175)
    ·
      refine ⟨5266418865977653860462263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510945910651769240308175 5266418865977653860462263)
      ·
        refine ⟨7899628298966480790693395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266418865977653860462263 7899628298966480790693395)
        ·
          refine ⟨11849442448449721186040093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7899628298966480790693395 11849442448449721186040093)
          ·
            refine ⟨4443540918168645444765035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11849442448449721186040093 4443540918168645444765035)
            ·
              refine ⟨6665311377252968167147553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443540918168645444765035 6665311377252968167147553)
              ·
                refine ⟨4998983532939726125360665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6665311377252968167147553 4998983532939726125360665)
                ·
                  refine ⟨3749237649704794594020499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4998983532939726125360665 3749237649704794594020499)
                  ·
                    refine ⟨5623856474557191891030749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3749237649704794594020499 5623856474557191891030749)
                    ·
                      refine ⟨2108946177958946959136531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5623856474557191891030749 2108946177958946959136531)
                      ·
                        rfl

theorem cell23_4107158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4107158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107158 prefixEnd_4107158 := by exact prefixLift 4107158
  have htrace : WordTrace (prefixWord ++ tailWord_4107158) baseStart_4107158 baseEnd_4107158 := by
    simpa [prefixWord, tailWord_4107158, baseEnd_4107158] using wordTrace_append hprefix tailTrace_4107158
  have hstable : (prefixWord ++ tailWord_4107158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107158).length < 2 ^ (prefixWord ++ tailWord_4107158).sum := by decide
  have hdescent : baseEnd_4107158 < baseStart_4107158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107164 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_4107164 : Nat := 118140960795 + 4107164 * 2 ^ 59
def prefixEnd_4107164 : Nat := 4983230072969 + 3 ^ 40 * 4107164 * 2
def baseEnd_4107164 : Nat := 2108949258842873935661503

theorem tailTrace_4107164 : CollatzResearch.WordTrace tailWord_4107164 prefixEnd_4107164 2108949258842873935661503 := by
  unfold tailWord_4107164
  simp only [CollatzResearch.WordTrace]
  refine ⟨74900288846226875305600273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99867051794969167074133697 74900288846226875305600273)
  ·
    refine ⟨56175216634670156479200205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74900288846226875305600273 56175216634670156479200205)
    ·
      refine ⟨21065706238001308679700077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56175216634670156479200205 21065706238001308679700077)
      ·
        refine ⟨7899639839250490754887529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21065706238001308679700077 7899639839250490754887529)
        ·
          refine ⟨5924729879437868066165647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7899639839250490754887529 5924729879437868066165647)
          ·
            refine ⟨8887094819156802099248471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924729879437868066165647 8887094819156802099248471)
            ·
              refine ⟨13330642228735203148872707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8887094819156802099248471 13330642228735203148872707)
              ·
                refine ⟨19995963343102804723309061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13330642228735203148872707 19995963343102804723309061)
                ·
                  refine ⟨3749243126831775885620449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19995963343102804723309061 3749243126831775885620449)
                  ·
                    refine ⟨2811932345123831914215337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3749243126831775885620449 2811932345123831914215337)
                    ·
                      refine ⟨2108949258842873935661503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811932345123831914215337 2108949258842873935661503)
                      ·
                        rfl

theorem cell23_4107164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_4107164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107164 prefixEnd_4107164 := by exact prefixLift 4107164
  have htrace : WordTrace (prefixWord ++ tailWord_4107164) baseStart_4107164 baseEnd_4107164 := by
    simpa [prefixWord, tailWord_4107164, baseEnd_4107164] using wordTrace_append hprefix tailTrace_4107164
  have hstable : (prefixWord ++ tailWord_4107164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107164).length < 2 ^ (prefixWord ++ tailWord_4107164).sum := by decide
  have hdescent : baseEnd_4107164 < baseStart_4107164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107170 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 7]
def baseStart_4107170 : Nat := 118140960795 + 4107170 * 2 ^ 59
def prefixEnd_4107170 : Nat := 4983230072969 + 3 ^ 40 * 4107170 * 2
def baseEnd_4107170 : Nat := 234328037747422323576275

theorem tailTrace_4107170 : CollatzResearch.WordTrace tailWord_4107170 prefixEnd_4107170 234328037747422323576275 := by
  unfold tailWord_4107170
  simp only [CollatzResearch.WordTrace]
  refine ⟨37450199132608003408979741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99867197686954675757279309 37450199132608003408979741)
  ·
    refine ⟨14043824674728001278367403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37450199132608003408979741 14043824674728001278367403)
    ·
      refine ⟨21065737012092001917551105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043824674728001278367403 21065737012092001917551105)
      ·
        refine ⟨15799302759069001438163329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21065737012092001917551105 15799302759069001438163329)
        ·
          refine ⟨11849477069301751078622497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15799302759069001438163329 11849477069301751078622497)
          ·
            refine ⟨8887107801976313308966873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11849477069301751078622497 8887107801976313308966873)
            ·
              refine ⟨6665330851482234981725155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8887107801976313308966873 6665330851482234981725155)
              ·
                refine ⟨9997996277223352472587733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665330851482234981725155 9997996277223352472587733)
                ·
                  refine ⟨234328037747422323576275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9997996277223352472587733 234328037747422323576275)
                  ·
                    rfl

theorem cell23_4107170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_4107170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107170 prefixEnd_4107170 := by exact prefixLift 4107170
  have htrace : WordTrace (prefixWord ++ tailWord_4107170) baseStart_4107170 baseEnd_4107170 := by
    simpa [prefixWord, tailWord_4107170, baseEnd_4107170] using wordTrace_append hprefix tailTrace_4107170
  have hstable : (prefixWord ++ tailWord_4107170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107170).length < 2 ^ (prefixWord ++ tailWord_4107170).sum := by decide
  have hdescent : baseEnd_4107170 < baseStart_4107170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107181 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4107181 : Nat := 118140960795 + 4107181 * 2 ^ 59
def prefixEnd_4107181 : Nat := 4983230072969 + 3 ^ 40 * 4107181 * 2
def baseEnd_4107181 : Nat := 2108957988014000369148925

theorem tailTrace_4107181 : CollatzResearch.WordTrace tailWord_4107181 prefixEnd_4107181 2108957988014000369148925 := by
  unfold tailWord_4107181
  simp only [CollatzResearch.WordTrace]
  refine ⟨149801197733392162514569397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99867465155594775009712931 149801197733392162514569397)
  ·
    refine ⟨14043862287505515235740881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149801197733392162514569397 14043862287505515235740881)
    ·
      refine ⟨10532896715629136426805661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14043862287505515235740881 10532896715629136426805661)
      ·
        refine ⟨3949836268360926160052123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10532896715629136426805661 3949836268360926160052123)
        ·
          refine ⟨5924754402541389240078185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949836268360926160052123 5924754402541389240078185)
          ·
            refine ⟨4443565801906041930058639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5924754402541389240078185 4443565801906041930058639)
            ·
              refine ⟨6665348702859062895087959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443565801906041930058639 6665348702859062895087959)
              ·
                refine ⟨9998023054288594342631939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665348702859062895087959 9998023054288594342631939)
                ·
                  refine ⟨14997034581432891513947909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9998023054288594342631939 14997034581432891513947909)
                  ·
                    refine ⟨2811943984018667158865233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14997034581432891513947909 2811943984018667158865233)
                    ·
                      refine ⟨2108957988014000369148925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2811943984018667158865233 2108957988014000369148925)
                      ·
                        rfl

theorem cell23_4107181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4107181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107181 prefixEnd_4107181 := by exact prefixLift 4107181
  have htrace : WordTrace (prefixWord ++ tailWord_4107181) baseStart_4107181 baseEnd_4107181 := by
    simpa [prefixWord, tailWord_4107181, baseEnd_4107181] using wordTrace_append hprefix tailTrace_4107181
  have hstable : (prefixWord ++ tailWord_4107181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107181).length < 2 ^ (prefixWord ++ tailWord_4107181).sum := by decide
  have hdescent : baseEnd_4107181 < baseStart_4107181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107220 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_4107220 : Nat := 118140960795 + 4107220 * 2 ^ 59
def prefixEnd_4107220 : Nat := 4983230072969 + 3 ^ 40 * 4107220 * 2
def baseEnd_4107220 : Nat := 2108978013759525716561245

theorem tailTrace_4107220 : CollatzResearch.WordTrace tailWord_4107220 prefixEnd_4107220 2108978013759525716561245 := by
  unfold tailWord_4107220
  simp only [CollatzResearch.WordTrace]
  refine ⟨74901310090125436087619557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99868413453500581450159409 74901310090125436087619557)
  ·
    refine ⟨14043995641898519266428667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74901310090125436087619557 14043995641898519266428667)
    ·
      refine ⟨21065993462847778899643001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043995641898519266428667 21065993462847778899643001)
      ·
        refine ⟨15799495097135834174732251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21065993462847778899643001 15799495097135834174732251)
        ·
          refine ⟨23699242645703751262098377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15799495097135834174732251 23699242645703751262098377)
          ·
            refine ⟨17774431984277813446573783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23699242645703751262098377 17774431984277813446573783)
            ·
              refine ⟨26661647976416720169860675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17774431984277813446573783 26661647976416720169860675)
              ·
                refine ⟨39992471964625080254791013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26661647976416720169860675 39992471964625080254791013)
                ·
                  refine ⟨7498588493367202547773315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39992471964625080254791013 7498588493367202547773315)
                  ·
                    refine ⟨11247882740050803821659973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7498588493367202547773315 11247882740050803821659973)
                    ·
                      refine ⟨2108978013759525716561245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11247882740050803821659973 2108978013759525716561245)
                      ·
                        rfl

theorem cell23_4107220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_4107220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107220 prefixEnd_4107220 := by exact prefixLift 4107220
  have htrace : WordTrace (prefixWord ++ tailWord_4107220) baseStart_4107220 baseEnd_4107220 := by
    simpa [prefixWord, tailWord_4107220, baseEnd_4107220] using wordTrace_append hprefix tailTrace_4107220
  have hstable : (prefixWord ++ tailWord_4107220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107220).length < 2 ^ (prefixWord ++ tailWord_4107220).sum := by decide
  have hdescent : baseEnd_4107220 < baseStart_4107220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107223 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_4107223 : Nat := 118140960795 + 4107223 * 2 ^ 59
def prefixEnd_4107223 : Nat := 4983230072969 + 3 ^ 40 * 4107223 * 2
def baseEnd_4107223 : Nat := 2108979554201489204823731

theorem tailTrace_4107223 : CollatzResearch.WordTrace tailWord_4107223 prefixEnd_4107223 2108979554201489204823731 := by
  unfold tailWord_4107223
  simp only [CollatzResearch.WordTrace]
  refine ⟨149802729599240003687598323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99868486399493335791732215 149802729599240003687598323)
  ·
    refine ⟨224704094398860005531397485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149802729599240003687598323 224704094398860005531397485)
    ·
      refine ⟨84264035399572502074274057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224704094398860005531397485 84264035399572502074274057)
      ·
        refine ⟨63198026549679376555705543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84264035399572502074274057 63198026549679376555705543)
        ·
          refine ⟨94797039824519064833558315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63198026549679376555705543 94797039824519064833558315)
          ·
            refine ⟨142195559736778597250337473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94797039824519064833558315 142195559736778597250337473)
            ·
              refine ⟨106646669802583947937753105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142195559736778597250337473 106646669802583947937753105)
              ·
                refine ⟨79985002351937960953314829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106646669802583947937753105 79985002351937960953314829)
                ·
                  refine ⟨29994375881976735357493061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79985002351937960953314829 29994375881976735357493061)
                  ·
                    refine ⟨5623945477870637879529949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29994375881976735357493061 5623945477870637879529949)
                    ·
                      refine ⟨2108979554201489204823731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5623945477870637879529949 2108979554201489204823731)
                      ·
                        rfl

theorem cell23_4107223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_4107223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107223 prefixEnd_4107223 := by exact prefixLift 4107223
  have htrace : WordTrace (prefixWord ++ tailWord_4107223) baseStart_4107223 baseEnd_4107223 := by
    simpa [prefixWord, tailWord_4107223, baseEnd_4107223] using wordTrace_append hprefix tailTrace_4107223
  have hstable : (prefixWord ++ tailWord_4107223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107223).length < 2 ^ (prefixWord ++ tailWord_4107223).sum := by decide
  have hdescent : baseEnd_4107223 < baseStart_4107223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107320 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 1, 6]
def baseStart_4107320 : Nat := 118140960795 + 4107320 * 2 ^ 59
def prefixEnd_4107320 : Nat := 4983230072969 + 3 ^ 40 * 4107320 * 2
def baseEnd_4107320 : Nat := 703009787274991775103595

theorem tailTrace_4107320 : CollatzResearch.WordTrace tailWord_4107320 prefixEnd_4107320 703009787274991775103595 := by
  unfold tailWord_4107320
  simp only [CollatzResearch.WordTrace]
  refine ⟨74903133739944294626939707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99870844986592392835919609 74903133739944294626939707)
  ·
    refine ⟨112354700609916441940409561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74903133739944294626939707 112354700609916441940409561)
    ·
      refine ⟨84266025457437331455307171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112354700609916441940409561 84266025457437331455307171)
      ·
        refine ⟨126399038186155997182960757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84266025457437331455307171 126399038186155997182960757)
        ·
          refine ⟨11849909829952124735902571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126399038186155997182960757 11849909829952124735902571)
          ·
            refine ⟨17774864744928187103853857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11849909829952124735902571 17774864744928187103853857)
            ·
              refine ⟨13331148558696140327890393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17774864744928187103853857 13331148558696140327890393)
              ·
                refine ⟨9998361419022105245917795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13331148558696140327890393 9998361419022105245917795)
                ·
                  refine ⟨14997542128533157868876693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9998361419022105245917795 14997542128533157868876693)
                  ·
                    refine ⟨703009787274991775103595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14997542128533157868876693 703009787274991775103595)
                    ·
                      rfl

theorem cell23_4107320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_4107320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107320 prefixEnd_4107320 := by exact prefixLift 4107320
  have htrace : WordTrace (prefixWord ++ tailWord_4107320) baseStart_4107320 baseEnd_4107320 := by
    simpa [prefixWord, tailWord_4107320, baseEnd_4107320] using wordTrace_append hprefix tailTrace_4107320
  have hstable : (prefixWord ++ tailWord_4107320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107320).length < 2 ^ (prefixWord ++ tailWord_4107320).sum := by decide
  have hdescent : baseEnd_4107320 < baseStart_4107320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107321 : List Nat := [1, 2, 1, 5, 2, 2, 2, 3, 1, 1, 3]
def baseStart_4107321 : Nat := 118140960795 + 4107321 * 2 ^ 59
def prefixEnd_4107321 : Nat := 4983230072969 + 3 ^ 40 * 4107321 * 2
def baseEnd_4107321 : Nat := 2109029875305629821398281

theorem tailTrace_4107321 : CollatzResearch.WordTrace tailWord_4107321 prefixEnd_4107321 2109029875305629821398281 := by
  unfold tailWord_4107321
  simp only [CollatzResearch.WordTrace]
  refine ⟨149806303952884966424665817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99870869301923310949777211 149806303952884966424665817)
  ·
    refine ⟨112354727964663724818499363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149806303952884966424665817 112354727964663724818499363)
    ·
      refine ⟨168532091946995587227749045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112354727964663724818499363 168532091946995587227749045)
      ·
        refine ⟨15799883620030836302601473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168532091946995587227749045 15799883620030836302601473)
        ·
          refine ⟨11849912715023127226951105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15799883620030836302601473 11849912715023127226951105)
          ·
            refine ⟨8887434536267345420213329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11849912715023127226951105 8887434536267345420213329)
            ·
              refine ⟨6665575902200509065159997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8887434536267345420213329 6665575902200509065159997)
              ·
                refine ⟨2499590963325190899434999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6665575902200509065159997 2499590963325190899434999)
                ·
                  refine ⟨3749386444987786349152499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499590963325190899434999 3749386444987786349152499)
                  ·
                    refine ⟨5624079667481679523728749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3749386444987786349152499 5624079667481679523728749)
                    ·
                      refine ⟨2109029875305629821398281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5624079667481679523728749 2109029875305629821398281)
                      ·
                        rfl

theorem cell23_4107321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_4107321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107321 prefixEnd_4107321 := by exact prefixLift 4107321
  have htrace : WordTrace (prefixWord ++ tailWord_4107321) baseStart_4107321 baseEnd_4107321 := by
    simpa [prefixWord, tailWord_4107321, baseEnd_4107321] using wordTrace_append hprefix tailTrace_4107321
  have hstable : (prefixWord ++ tailWord_4107321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107321).length < 2 ^ (prefixWord ++ tailWord_4107321).sum := by decide
  have hdescent : baseEnd_4107321 < baseStart_4107321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107324 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_4107324 : Nat := 118140960795 + 4107324 * 2 ^ 59
def prefixEnd_4107324 : Nat := 4983230072969 + 3 ^ 40 * 4107324 * 2
def baseEnd_4107324 : Nat := 703010471915864436553589

theorem tailTrace_4107324 : CollatzResearch.WordTrace tailWord_4107324 prefixEnd_4107324 703010471915864436553589 := by
  unfold tailWord_4107324
  simp only [CollatzResearch.WordTrace]
  refine ⟨74903206685937048968512513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99870942247916065291350017 74903206685937048968512513)
  ·
    refine ⟨56177405014452786726384385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74903206685937048968512513 56177405014452786726384385)
    ·
      refine ⟨42133053760839590044788289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56177405014452786726384385 42133053760839590044788289)
      ·
        refine ⟨31599790320629692533591217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42133053760839590044788289 31599790320629692533591217)
        ·
          refine ⟨23699842740472269400193413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31599790320629692533591217 23699842740472269400193413)
          ·
            refine ⟨4443720513838550512536265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23699842740472269400193413 4443720513838550512536265)
            ·
              refine ⟨3332790385378912884402199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443720513838550512536265 3332790385378912884402199)
              ·
                refine ⟨4999185578068369326603299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332790385378912884402199 4999185578068369326603299)
                ·
                  refine ⟨7498778367102553989904949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4999185578068369326603299 7498778367102553989904949)
                  ·
                    refine ⟨703010471915864436553589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7498778367102553989904949 703010471915864436553589)
                    ·
                      rfl

theorem cell23_4107324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_4107324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107324 prefixEnd_4107324 := by exact prefixLift 4107324
  have htrace : WordTrace (prefixWord ++ tailWord_4107324) baseStart_4107324 baseEnd_4107324 := by
    simpa [prefixWord, tailWord_4107324, baseEnd_4107324] using wordTrace_append hprefix tailTrace_4107324
  have hstable : (prefixWord ++ tailWord_4107324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107324).length < 2 ^ (prefixWord ++ tailWord_4107324).sum := by decide
  have hdescent : baseEnd_4107324 < baseStart_4107324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107327 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 7, 2, 2]
def baseStart_4107327 : Nat := 118140960795 + 4107327 * 2 ^ 59
def prefixEnd_4107327 : Nat := 4983230072969 + 3 ^ 40 * 4107327 * 2
def baseEnd_4107327 : Nat := 2109032956189556797923253

theorem tailTrace_4107327 : CollatzResearch.WordTrace tailWord_4107327 prefixEnd_4107327 2109032956189556797923253 := by
  unfold tailWord_4107327
  simp only [CollatzResearch.WordTrace]
  refine ⟨149806522790863229449384235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99871015193908819632922823 149806522790863229449384235)
  ·
    refine ⟨224709784186294844174076353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149806522790863229449384235 224709784186294844174076353)
    ·
      refine ⟨168532338139721133130557265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224709784186294844174076353 168532338139721133130557265)
      ·
        refine ⟨126399253604790849847917949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168532338139721133130557265 126399253604790849847917949)
        ·
          refine ⟨47399720101796568692969231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126399253604790849847917949 47399720101796568692969231)
          ·
            refine ⟨71099580152694853039453847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47399720101796568692969231 71099580152694853039453847)
            ·
              refine ⟨106649370229042279559180771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71099580152694853039453847 106649370229042279559180771)
              ·
                refine ⟨159974055343563419338771157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106649370229042279559180771 159974055343563419338771157)
                ·
                  refine ⟨3749391922114767640752449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 159974055343563419338771157 3749391922114767640752449)
                  ·
                    refine ⟨2812043941586075730564337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3749391922114767640752449 2812043941586075730564337)
                    ·
                      refine ⟨2109032956189556797923253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812043941586075730564337 2109032956189556797923253)
                      ·
                        rfl

theorem cell23_4107327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_4107327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107327 prefixEnd_4107327 := by exact prefixLift 4107327
  have htrace : WordTrace (prefixWord ++ tailWord_4107327) baseStart_4107327 baseEnd_4107327 := by
    simpa [prefixWord, tailWord_4107327, baseEnd_4107327] using wordTrace_append hprefix tailTrace_4107327
  have hstable : (prefixWord ++ tailWord_4107327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107327).length < 2 ^ (prefixWord ++ tailWord_4107327).sum := by decide
  have hdescent : baseEnd_4107327 < baseStart_4107327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107353 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_4107353 : Nat := 118140960795 + 4107353 * 2 ^ 59
def prefixEnd_4107353 : Nat := 4983230072969 + 3 ^ 40 * 4107353 * 2
def baseEnd_4107353 : Nat := 2109046306686573696198133

theorem tailTrace_4107353 : CollatzResearch.WordTrace tailWord_4107353 prefixEnd_4107353 2109046306686573696198133 := by
  unfold tailWord_4107353
  simp only [CollatzResearch.WordTrace]
  refine ⟨149807471088769035889830713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99871647392512690593220475 149807471088769035889830713)
  ·
    refine ⟨112355603316576776917373035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149807471088769035889830713 112355603316576776917373035)
    ·
      refine ⟨168533404974865165376059553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112355603316576776917373035 168533404974865165376059553)
      ·
        refine ⟨126400053731148874032044665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168533404974865165376059553 126400053731148874032044665)
        ·
          refine ⟨94800040298361655524033499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126400053731148874032044665 94800040298361655524033499)
          ·
            refine ⟨142200060447542483286050249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94800040298361655524033499 142200060447542483286050249)
            ·
              refine ⟨106650045335656862464537687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142200060447542483286050249 106650045335656862464537687)
              ·
                refine ⟨159975068003485293696806531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106650045335656862464537687 159975068003485293696806531)
                ·
                  refine ⟨239962602005227940545209797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159975068003485293696806531 239962602005227940545209797)
                  ·
                    refine ⟨44992987875980238852226837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239962602005227940545209797 44992987875980238852226837)
                    ·
                      refine ⟨2109046306686573696198133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44992987875980238852226837 2109046306686573696198133)
                      ·
                        rfl

theorem cell23_4107353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_4107353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107353 prefixEnd_4107353 := by exact prefixLift 4107353
  have htrace : WordTrace (prefixWord ++ tailWord_4107353) baseStart_4107353 baseEnd_4107353 := by
    simpa [prefixWord, tailWord_4107353, baseEnd_4107353] using wordTrace_append hprefix tailTrace_4107353
  have hstable : (prefixWord ++ tailWord_4107353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107353).length < 2 ^ (prefixWord ++ tailWord_4107353).sum := by decide
  have hdescent : baseEnd_4107353 < baseStart_4107353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107367 : List Nat := [1, 1, 5, 1, 1, 5, 2, 7]
def baseStart_4107367 : Nat := 118140960795 + 4107367 * 2 ^ 59
def prefixEnd_4107367 : Nat := 4983230072969 + 3 ^ 40 * 4107367 * 2
def baseEnd_4107367 : Nat := 78113092422805060793447

theorem tailTrace_4107367 : CollatzResearch.WordTrace tailWord_4107367 prefixEnd_4107367 78113092422805060793447 := by
  unfold tailWord_4107367
  simp only [CollatzResearch.WordTrace]
  refine ⟨149807981710718316280840355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99871987807145544187226903 149807981710718316280840355)
  ·
    refine ⟨224711972566077474421260533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149807981710718316280840355 224711972566077474421260533)
    ·
      refine ⟨21066747428069763226993175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224711972566077474421260533 21066747428069763226993175)
      ·
        refine ⟨31600121142104644840489763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21066747428069763226993175 31600121142104644840489763)
        ·
          refine ⟨47400181713156967260734645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31600121142104644840489763 47400181713156967260734645)
          ·
            refine ⟨4443767035608465680693873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47400181713156967260734645 4443767035608465680693873)
            ·
              refine ⟨3332825276706349260520405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443767035608465680693873 3332825276706349260520405)
              ·
                refine ⟨78113092422805060793447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3332825276706349260520405 78113092422805060793447)
                ·
                  rfl

theorem cell23_4107367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 7].length) (baseStart_4107367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107367 prefixEnd_4107367 := by exact prefixLift 4107367
  have htrace : WordTrace (prefixWord ++ tailWord_4107367) baseStart_4107367 baseEnd_4107367 := by
    simpa [prefixWord, tailWord_4107367, baseEnd_4107367] using wordTrace_append hprefix tailTrace_4107367
  have hstable : (prefixWord ++ tailWord_4107367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107367).length < 2 ^ (prefixWord ++ tailWord_4107367).sum := by decide
  have hdescent : baseEnd_4107367 < baseStart_4107367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107446 : List Nat := [5, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4107446 : Nat := 118140960795 + 4107446 * 2 ^ 59
def prefixEnd_4107446 : Nat := 4983230072969 + 3 ^ 40 * 4107446 * 2
def baseEnd_4107446 : Nat := 2109094060387441832335207

theorem tailTrace_4107446 : CollatzResearch.WordTrace tailWord_4107446 prefixEnd_4107446 2109094060387441832335207 := by
  unfold tailWord_4107446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363178942339507048310387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99873908718288075181977461 9363178942339507048310387)
  ·
    refine ⟨14044768413509260572465581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9363178942339507048310387 14044768413509260572465581)
    ·
      refine ⟨5266788155065972714674593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14044768413509260572465581 5266788155065972714674593)
      ·
        refine ⟨3950091116299479536005945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5266788155065972714674593 3950091116299479536005945)
        ·
          refine ⟨2962568337224609652004459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3950091116299479536005945 2962568337224609652004459)
          ·
            refine ⟨4443852505836914478006689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962568337224609652004459 4443852505836914478006689)
            ·
              refine ⟨3332889379377685858505017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443852505836914478006689 3332889379377685858505017)
              ·
                refine ⟨2499667034533264393878763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3332889379377685858505017 2499667034533264393878763)
                ·
                  refine ⟨3749500551799896590818145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499667034533264393878763 3749500551799896590818145)
                  ·
                    refine ⟨2812125413849922443113609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3749500551799896590818145 2812125413849922443113609)
                    ·
                      refine ⟨2109094060387441832335207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812125413849922443113609 2109094060387441832335207)
                      ·
                        rfl

theorem cell23_4107446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4107446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107446 prefixEnd_4107446 := by exact prefixLift 4107446
  have htrace : WordTrace (prefixWord ++ tailWord_4107446) baseStart_4107446 baseEnd_4107446 := by
    simpa [prefixWord, tailWord_4107446, baseEnd_4107446] using wordTrace_append hprefix tailTrace_4107446
  have hstable : (prefixWord ++ tailWord_4107446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107446).length < 2 ^ (prefixWord ++ tailWord_4107446).sum := by decide
  have hdescent : baseEnd_4107446 < baseStart_4107446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107487 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 2, 5]
def baseStart_4107487 : Nat := 118140960795 + 4107487 * 2 ^ 59
def prefixEnd_4107487 : Nat := 4983230072969 + 3 ^ 40 * 4107487 * 2
def baseEnd_4107487 : Nat := 703038371031425390640839

theorem tailTrace_4107487 : CollatzResearch.WordTrace tailWord_4107487 prefixEnd_4107487 703038371031425390640839 := by
  unfold tailWord_4107487
  simp only [CollatzResearch.WordTrace]
  refine ⟨149812358470283576775208715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99874905646855717850139143 149812358470283576775208715)
  ·
    refine ⟨224718537705425365162813073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149812358470283576775208715 224718537705425365162813073)
    ·
      refine ⟨168538903279069023872109805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224718537705425365162813073 168538903279069023872109805)
      ·
        refine ⟨63202088729650883952041177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168538903279069023872109805 63202088729650883952041177)
        ·
          refine ⟨47401566547238162964030883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63202088729650883952041177 47401566547238162964030883)
          ·
            refine ⟨71102349820857244446046325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47401566547238162964030883 71102349820857244446046325)
            ·
              refine ⟨6665845295705366666816843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71102349820857244446046325 6665845295705366666816843)
              ·
                refine ⟨9998767943558050000225265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665845295705366666816843 9998767943558050000225265)
                ·
                  refine ⟨7499075957668537500168949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9998767943558050000225265 7499075957668537500168949)
                  ·
                    refine ⟨703038371031425390640839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7499075957668537500168949 703038371031425390640839)
                    ·
                      rfl

theorem cell23_4107487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_4107487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107487 prefixEnd_4107487 := by exact prefixLift 4107487
  have htrace : WordTrace (prefixWord ++ tailWord_4107487) baseStart_4107487 baseEnd_4107487 := by
    simpa [prefixWord, tailWord_4107487, baseEnd_4107487] using wordTrace_append hprefix tailTrace_4107487
  have hstable : (prefixWord ++ tailWord_4107487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107487).length < 2 ^ (prefixWord ++ tailWord_4107487).sum := by decide
  have hdescent : baseEnd_4107487 < baseStart_4107487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107508 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 7]
def baseStart_4107508 : Nat := 118140960795 + 4107508 * 2 ^ 59
def prefixEnd_4107508 : Nat := 4983230072969 + 3 ^ 40 * 4107508 * 2
def baseEnd_4107508 : Nat := 234347321798668954417769

theorem tailTrace_4107508 : CollatzResearch.WordTrace tailWord_4107508 prefixEnd_4107508 234347321798668954417769 := by
  unfold tailWord_4107508
  simp only [CollatzResearch.WordTrace]
  refine ⟨74906562201603748680861589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99875416268804998241148785 74906562201603748680861589)
  ·
    refine ⟨3511245103200175719415387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74906562201603748680861589 3511245103200175719415387)
    ·
      refine ⟨5266867654800263579123081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511245103200175719415387 5266867654800263579123081)
      ·
        refine ⟨3950150741100197684342311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5266867654800263579123081 3950150741100197684342311)
        ·
          refine ⟨5925226111650296526513467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950150741100197684342311 5925226111650296526513467)
          ·
            refine ⟨8887839167475444789770201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5925226111650296526513467 8887839167475444789770201)
            ·
              refine ⟨6665879375606583592327651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8887839167475444789770201 6665879375606583592327651)
              ·
                refine ⟨9998819063409875388491477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665879375606583592327651 9998819063409875388491477)
                ·
                  refine ⟨234347321798668954417769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9998819063409875388491477 234347321798668954417769)
                  ·
                    rfl

theorem cell23_4107508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_4107508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107508 prefixEnd_4107508 := by exact prefixLift 4107508
  have htrace : WordTrace (prefixWord ++ tailWord_4107508) baseStart_4107508 baseEnd_4107508 := by
    simpa [prefixWord, tailWord_4107508, baseEnd_4107508] using wordTrace_append hprefix tailTrace_4107508
  have hstable : (prefixWord ++ tailWord_4107508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107508).length < 2 ^ (prefixWord ++ tailWord_4107508).sum := by decide
  have hdescent : baseEnd_4107508 < baseStart_4107508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107520 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_4107520 : Nat := 118140960795 + 4107520 * 2 ^ 59
def prefixEnd_4107520 : Nat := 4983230072969 + 3 ^ 40 * 4107520 * 2
def baseEnd_4107520 : Nat := 2109132057955874542809865

theorem tailTrace_4107520 : CollatzResearch.WordTrace tailWord_4107520 prefixEnd_4107520 2109132057955874542809865 := by
  unfold tailWord_4107520
  simp only [CollatzResearch.WordTrace]
  refine ⟨74906781039582011705580007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99875708052776015607440009 74906781039582011705580007)
  ·
    refine ⟨112360171559373017558370011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74906781039582011705580007 112360171559373017558370011)
    ·
      refine ⟨168540257339059526337555017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112360171559373017558370011 168540257339059526337555017)
      ·
        refine ⟨126405193004294644753166263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168540257339059526337555017 126405193004294644753166263)
        ·
          refine ⟨189607789506441967129749395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126405193004294644753166263 189607789506441967129749395)
          ·
            refine ⟨284411684259662950694624093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189607789506441967129749395 284411684259662950694624093)
            ·
              refine ⟨106654381597373606510484035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284411684259662950694624093 106654381597373606510484035)
              ·
                refine ⟨159981572396060409765726053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106654381597373606510484035 159981572396060409765726053)
                ·
                  refine ⟨29996544824261326831073635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159981572396060409765726053 29996544824261326831073635)
                  ·
                    refine ⟨44994817236391990246610453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29996544824261326831073635 44994817236391990246610453)
                    ·
                      refine ⟨2109132057955874542809865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44994817236391990246610453 2109132057955874542809865)
                      ·
                        rfl

theorem cell23_4107520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_4107520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107520 prefixEnd_4107520 := by exact prefixLift 4107520
  have htrace : WordTrace (prefixWord ++ tailWord_4107520) baseStart_4107520 baseEnd_4107520 := by
    simpa [prefixWord, tailWord_4107520, baseEnd_4107520] using wordTrace_append hprefix tailTrace_4107520
  have hstable : (prefixWord ++ tailWord_4107520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107520).length < 2 ^ (prefixWord ++ tailWord_4107520).sum := by decide
  have hdescent : baseEnd_4107520 < baseStart_4107520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107534 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_4107534 : Nat := 118140960795 + 4107534 * 2 ^ 59
def prefixEnd_4107534 : Nat := 4983230072969 + 3 ^ 40 * 4107534 * 2
def baseEnd_4107534 : Nat := 703046415561679162678267

theorem tailTrace_4107534 : CollatzResearch.WordTrace tailWord_4107534 prefixEnd_4107534 703046415561679162678267 := by
  unfold tailWord_4107534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18726759087639162975271207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99876048467408869201446437 18726759087639162975271207)
  ·
    refine ⟨28090138631458744462906811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18726759087639162975271207 28090138631458744462906811)
    ·
      refine ⟨42135207947188116694360217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28090138631458744462906811 42135207947188116694360217)
      ·
        refine ⟨31601405960391087520770163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42135207947188116694360217 31601405960391087520770163)
        ·
          refine ⟨47402108940586631281155245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31601405960391087520770163 47402108940586631281155245)
          ·
            refine ⟨17775790852719986730433217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47402108940586631281155245 17775790852719986730433217)
            ·
              refine ⟨13331843139539990047824913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17775790852719986730433217 13331843139539990047824913)
              ·
                refine ⟨9998882354654992535868685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13331843139539990047824913 9998882354654992535868685)
                ·
                  refine ⟨3749580882995622200950757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9998882354654992535868685 3749580882995622200950757)
                  ·
                    refine ⟨703046415561679162678267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3749580882995622200950757 703046415561679162678267)
                    ·
                      rfl

theorem cell23_4107534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_4107534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107534 prefixEnd_4107534 := by exact prefixLift 4107534
  have htrace : WordTrace (prefixWord ++ tailWord_4107534) baseStart_4107534 baseEnd_4107534 := by
    simpa [prefixWord, tailWord_4107534, baseEnd_4107534] using wordTrace_append hprefix tailTrace_4107534
  have hstable : (prefixWord ++ tailWord_4107534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107534).length < 2 ^ (prefixWord ++ tailWord_4107534).sum := by decide
  have hdescent : baseEnd_4107534 < baseStart_4107534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107581 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 6]
def baseStart_4107581 : Nat := 118140960795 + 4107581 * 2 ^ 59
def prefixEnd_4107581 : Nat := 4983230072969 + 3 ^ 40 * 4107581 * 2
def baseEnd_4107581 : Nat := 234351486697310978238565

theorem tailTrace_4107581 : CollatzResearch.WordTrace tailWord_4107581 prefixEnd_4107581 234351486697310978238565 := by
  unfold tailWord_4107581
  simp only [CollatzResearch.WordTrace]
  refine ⟨149815786931943030829130597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99877191287962020552753731 149815786931943030829130597)
  ·
    refine ⟨28090460049739318280461987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149815786931943030829130597 28090460049739318280461987)
    ·
      refine ⟨42135690074608977420692981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28090460049739318280461987 42135690074608977420692981)
      ·
        refine ⟨3950220944494591633189967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42135690074608977420692981 3950220944494591633189967)
        ·
          refine ⟨5925331416741887449784951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950220944494591633189967 5925331416741887449784951)
          ·
            refine ⟨8887997125112831174677427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5925331416741887449784951 8887997125112831174677427)
            ·
              refine ⟨13331995687669246762016141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8887997125112831174677427 13331995687669246762016141)
              ·
                refine ⟨4999498382875967535756053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13331995687669246762016141 4999498382875967535756053)
                ·
                  refine ⟨234351486697310978238565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4999498382875967535756053 234351486697310978238565)
                  ·
                    rfl

theorem cell23_4107581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_4107581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107581 prefixEnd_4107581 := by exact prefixLift 4107581
  have htrace : WordTrace (prefixWord ++ tailWord_4107581) baseStart_4107581 baseEnd_4107581 := by
    simpa [prefixWord, tailWord_4107581, baseEnd_4107581] using wordTrace_append hprefix tailTrace_4107581
  have hstable : (prefixWord ++ tailWord_4107581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107581).length < 2 ^ (prefixWord ++ tailWord_4107581).sum := by decide
  have hdescent : baseEnd_4107581 < baseStart_4107581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107584 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 4, 3, 2]
def baseStart_4107584 : Nat := 118140960795 + 4107584 * 2 ^ 59
def prefixEnd_4107584 : Nat := 4983230072969 + 3 ^ 40 * 4107584 * 2
def baseEnd_4107584 : Nat := 2109164920717762292409571

theorem tailTrace_4107584 : CollatzResearch.WordTrace tailWord_4107584 prefixEnd_4107584 2109164920717762292409571 := by
  unfold tailWord_4107584
  simp only [CollatzResearch.WordTrace]
  refine ⟨74907948175466081170744903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99877264233954774894326537 74907948175466081170744903)
  ·
    refine ⟨112361922263199121756117355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74907948175466081170744903 112361922263199121756117355)
    ·
      refine ⟨168542883394798682634176033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112361922263199121756117355 168542883394798682634176033)
      ·
        refine ⟨126407162546099011975632025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168542883394798682634176033 126407162546099011975632025)
        ·
          refine ⟨94805371909574258981724019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126407162546099011975632025 94805371909574258981724019)
          ·
            refine ⟨142208057864361388472586029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94805371909574258981724019 142208057864361388472586029)
            ·
              refine ⟨53328021699135520677219761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142208057864361388472586029 53328021699135520677219761)
              ·
                refine ⟨39996016274351640507914821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53328021699135520677219761 39996016274351640507914821)
                ·
                  refine ⟨7499253051440932595234029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39996016274351640507914821 7499253051440932595234029)
                  ·
                    refine ⟨2812219894290349723212761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7499253051440932595234029 2812219894290349723212761)
                    ·
                      refine ⟨2109164920717762292409571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812219894290349723212761 2109164920717762292409571)
                      ·
                        rfl

theorem cell23_4107584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_4107584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107584 prefixEnd_4107584 := by exact prefixLift 4107584
  have htrace : WordTrace (prefixWord ++ tailWord_4107584) baseStart_4107584 baseEnd_4107584 := by
    simpa [prefixWord, tailWord_4107584, baseEnd_4107584] using wordTrace_append hprefix tailTrace_4107584
  have hstable : (prefixWord ++ tailWord_4107584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107584).length < 2 ^ (prefixWord ++ tailWord_4107584).sum := by decide
  have hdescent : baseEnd_4107584 < baseStart_4107584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107601 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 2, 3, 2]
def baseStart_4107601 : Nat := 118140960795 + 4107601 * 2 ^ 59
def prefixEnd_4107601 : Nat := 4983230072969 + 3 ^ 40 * 4107601 * 2
def baseEnd_4107601 : Nat := 2109173649888888725896993

theorem tailTrace_4107601 : CollatzResearch.WordTrace tailWord_4107601 prefixEnd_4107601 2109173649888888725896993 := by
  unfold tailWord_4107601
  simp only [CollatzResearch.WordTrace]
  refine ⟨149816516391870574244858657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99877677594580382829905771 149816516391870574244858657)
  ·
    refine ⟨112362387293902930683643993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149816516391870574244858657 112362387293902930683643993)
    ·
      refine ⟨84271790470427198012732995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112362387293902930683643993 84271790470427198012732995)
      ·
        refine ⟨126407685705640797019099493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84271790470427198012732995 126407685705640797019099493)
        ·
          refine ⟨23701441069807649441081155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126407685705640797019099493 23701441069807649441081155)
          ·
            refine ⟨35552161604711474161621733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23701441069807649441081155 35552161604711474161621733)
            ·
              refine ⟨6666030300883401405304075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35552161604711474161621733 6666030300883401405304075)
              ·
                refine ⟨9999045451325102107956113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6666030300883401405304075 9999045451325102107956113)
                ·
                  refine ⟨7499284088493826580967085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9999045451325102107956113 7499284088493826580967085)
                  ·
                    refine ⟨2812231533185184967862657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7499284088493826580967085 2812231533185184967862657)
                    ·
                      refine ⟨2109173649888888725896993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812231533185184967862657 2109173649888888725896993)
                      ·
                        rfl

theorem cell23_4107601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_4107601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107601 prefixEnd_4107601 := by exact prefixLift 4107601
  have htrace : WordTrace (prefixWord ++ tailWord_4107601) baseStart_4107601 baseEnd_4107601 := by
    simpa [prefixWord, tailWord_4107601, baseEnd_4107601] using wordTrace_append hprefix tailTrace_4107601
  have hstable : (prefixWord ++ tailWord_4107601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107601).length < 2 ^ (prefixWord ++ tailWord_4107601).sum := by decide
  have hdescent : baseEnd_4107601 < baseStart_4107601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107607 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 3, 6]
def baseStart_4107607 : Nat := 118140960795 + 4107607 * 2 ^ 59
def prefixEnd_4107607 : Nat := 4983230072969 + 3 ^ 40 * 4107607 * 2
def baseEnd_4107607 : Nat := 703058910257605234140655

theorem tailTrace_4107607 : CollatzResearch.WordTrace tailWord_4107607 prefixEnd_4107607 703058910257605234140655 := by
  unfold tailWord_4107607
  simp only [CollatzResearch.WordTrace]
  refine ⟨149816735229848837269577075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99877823486565891513051383 149816735229848837269577075)
  ·
    refine ⟨224725102844773255904365613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149816735229848837269577075 224725102844773255904365613)
    ·
      refine ⟨84271913566789970964137105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224725102844773255904365613 84271913566789970964137105)
      ·
        refine ⟨63203935175092478223102829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84271913566789970964137105 63203935175092478223102829)
        ·
          refine ⟨23701475690659679333663561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63203935175092478223102829 23701475690659679333663561)
          ·
            refine ⟨17776106767994759500247671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23701475690659679333663561 17776106767994759500247671)
            ·
              refine ⟨26664160151992139250371507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17776106767994759500247671 26664160151992139250371507)
              ·
                refine ⟨39996240227988208875557261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26664160151992139250371507 39996240227988208875557261)
                ·
                  refine ⟨14998590085495578328333973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39996240227988208875557261 14998590085495578328333973)
                  ·
                    refine ⟨703058910257605234140655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14998590085495578328333973 703058910257605234140655)
                    ·
                      rfl

theorem cell23_4107607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_4107607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107607 prefixEnd_4107607 := by exact prefixLift 4107607
  have htrace : WordTrace (prefixWord ++ tailWord_4107607) baseStart_4107607 baseEnd_4107607 := by
    simpa [prefixWord, tailWord_4107607, baseEnd_4107607] using wordTrace_append hprefix tailTrace_4107607
  have hstable : (prefixWord ++ tailWord_4107607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107607).length < 2 ^ (prefixWord ++ tailWord_4107607).sum := by decide
  have hdescent : baseEnd_4107607 < baseStart_4107607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107631 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 3, 2, 2]
def baseStart_4107631 : Nat := 118140960795 + 4107631 * 2 ^ 59
def prefixEnd_4107631 : Nat := 4983230072969 + 3 ^ 40 * 4107631 * 2
def baseEnd_4107631 : Nat := 2109189054308523608521855

theorem tailTrace_4107631 : CollatzResearch.WordTrace tailWord_4107631 prefixEnd_4107631 2109189054308523608521855 := by
  unfold tailWord_4107631
  simp only [CollatzResearch.WordTrace]
  refine ⟨149817610581761889368450747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99878407054507926245633831 149817610581761889368450747)
  ·
    refine ⟨224726415872642834052676121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149817610581761889368450747 224726415872642834052676121)
    ·
      refine ⟨168544811904482125539507091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224726415872642834052676121 168544811904482125539507091)
      ·
        refine ⟨252817217856723188309260637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168544811904482125539507091 252817217856723188309260637)
        ·
          refine ⟨94806456696271195615972739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252817217856723188309260637 94806456696271195615972739)
          ·
            refine ⟨142209685044406793423959109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94806456696271195615972739 142209685044406793423959109)
            ·
              refine ⟨26664315945826273766992333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142209685044406793423959109 26664315945826273766992333)
              ·
                refine ⟨9999118479684852662622125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26664315945826273766992333 9999118479684852662622125)
                ·
                  refine ⟨3749669429881819748483297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9999118479684852662622125 3749669429881819748483297)
                  ·
                    refine ⟨2812252072411364811362473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3749669429881819748483297 2812252072411364811362473)
                    ·
                      refine ⟨2109189054308523608521855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812252072411364811362473 2109189054308523608521855)
                      ·
                        rfl

theorem cell23_4107631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 2, 2].length) (baseStart_4107631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107631 prefixEnd_4107631 := by exact prefixLift 4107631
  have htrace : WordTrace (prefixWord ++ tailWord_4107631) baseStart_4107631 baseEnd_4107631 := by
    simpa [prefixWord, tailWord_4107631, baseEnd_4107631] using wordTrace_append hprefix tailTrace_4107631
  have hstable : (prefixWord ++ tailWord_4107631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107631).length < 2 ^ (prefixWord ++ tailWord_4107631).sum := by decide
  have hdescent : baseEnd_4107631 < baseStart_4107631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107634 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_4107634 : Nat := 118140960795 + 4107634 * 2 ^ 59
def prefixEnd_4107634 : Nat := 4983230072969 + 3 ^ 40 * 4107634 * 2
def baseEnd_4107634 : Nat := 2109190594750487096784341

theorem tailTrace_4107634 : CollatzResearch.WordTrace tailWord_4107634 prefixEnd_4107634 2109190594750487096784341 := by
  unfold tailWord_4107634
  simp only [CollatzResearch.WordTrace]
  refine ⟨37454430000187755220202489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99878480000500680587206637 37454430000187755220202489)
  ·
    refine ⟨28090822500140816415151867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37454430000187755220202489 28090822500140816415151867)
    ·
      refine ⟨42136233750211224622727801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28090822500140816415151867 42136233750211224622727801)
      ·
        refine ⟨31602175312658418467045851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42136233750211224622727801 31602175312658418467045851)
        ·
          refine ⟨47403262968987627700568777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31602175312658418467045851 47403262968987627700568777)
          ·
            refine ⟨35552447226740720775426583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47403262968987627700568777 35552447226740720775426583)
            ·
              refine ⟨53328670840111081163139875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35552447226740720775426583 53328670840111081163139875)
              ·
                refine ⟨79993006260166621744709813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53328670840111081163139875 79993006260166621744709813)
                ·
                  refine ⟨7499344336890620788566545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79993006260166621744709813 7499344336890620788566545)
                  ·
                    refine ⟨5624508252667965591424909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7499344336890620788566545 5624508252667965591424909)
                    ·
                      refine ⟨2109190594750487096784341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5624508252667965591424909 2109190594750487096784341)
                      ·
                        rfl

theorem cell23_4107634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_4107634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107634 prefixEnd_4107634 := by exact prefixLift 4107634
  have htrace : WordTrace (prefixWord ++ tailWord_4107634) baseStart_4107634 baseEnd_4107634 := by
    simpa [prefixWord, tailWord_4107634, baseEnd_4107634] using wordTrace_append hprefix tailTrace_4107634
  have hstable : (prefixWord ++ tailWord_4107634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107634).length < 2 ^ (prefixWord ++ tailWord_4107634).sum := by decide
  have hdescent : baseEnd_4107634 < baseStart_4107634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107644 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_4107644 : Nat := 118140960795 + 4107644 * 2 ^ 59
def prefixEnd_4107644 : Nat := 4983230072969 + 3 ^ 40 * 4107644 * 2
def baseEnd_4107644 : Nat := 2109195729557032057659295

theorem tailTrace_4107644 : CollatzResearch.WordTrace tailWord_4107644 prefixEnd_4107644 2109195729557032057659295 := by
  unfold tailWord_4107644
  simp only [CollatzResearch.WordTrace]
  refine ⟨74909042365357396294336993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99878723153809861725782657 74909042365357396294336993)
  ·
    refine ⟨56181781774018047220752745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74909042365357396294336993 56181781774018047220752745)
    ·
      refine ⟨42136336330513535415564559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56181781774018047220752745 42136336330513535415564559)
      ·
        refine ⟨63204504495770303123346839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42136336330513535415564559 63204504495770303123346839)
        ·
          refine ⟨94806756743655454685020259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63204504495770303123346839 94806756743655454685020259)
          ·
            refine ⟨142210135115483182027530389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94806756743655454685020259 142210135115483182027530389)
            ·
              refine ⟨6666100083538274157540487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142210135115483182027530389 6666100083538274157540487)
              ·
                refine ⟨9999150125307411236310731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6666100083538274157540487 9999150125307411236310731)
                ·
                  refine ⟨14998725187961116854466097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9999150125307411236310731 14998725187961116854466097)
                  ·
                    refine ⟨11249043890970837640849573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14998725187961116854466097 11249043890970837640849573)
                    ·
                      refine ⟨2109195729557032057659295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11249043890970837640849573 2109195729557032057659295)
                      ·
                        rfl

theorem cell23_4107644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_4107644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107644 prefixEnd_4107644 := by exact prefixLift 4107644
  have htrace : WordTrace (prefixWord ++ tailWord_4107644) baseStart_4107644 baseEnd_4107644 := by
    simpa [prefixWord, tailWord_4107644, baseEnd_4107644] using wordTrace_append hprefix tailTrace_4107644
  have hstable : (prefixWord ++ tailWord_4107644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107644).length < 2 ^ (prefixWord ++ tailWord_4107644).sum := by decide
  have hdescent : baseEnd_4107644 < baseStart_4107644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107668 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_4107668 : Nat := 118140960795 + 4107668 * 2 ^ 59
def prefixEnd_4107668 : Nat := 4983230072969 + 3 ^ 40 * 4107668 * 2
def baseEnd_4107668 : Nat := 2109208053092739963759185

theorem tailTrace_4107668 : CollatzResearch.WordTrace tailWord_4107668 prefixEnd_4107668 2109208053092739963759185 := by
  unfold tailWord_4107668
  simp only [CollatzResearch.WordTrace]
  refine ⟨74909480041313922343773829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99879306721751896458365105 74909480041313922343773829)
  ·
    refine ⟨14045527507746360439457593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74909480041313922343773829 14045527507746360439457593)
    ·
      refine ⟨10534145630809770329593195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14045527507746360439457593 10534145630809770329593195)
      ·
        refine ⟨15801218446214655494389793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10534145630809770329593195 15801218446214655494389793)
        ·
          refine ⟨11850913834660991620792345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15801218446214655494389793 11850913834660991620792345)
          ·
            refine ⟨8888185375995743715594259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11850913834660991620792345 8888185375995743715594259)
            ·
              refine ⟨13332278063993615573391389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8888185375995743715594259 13332278063993615573391389)
              ·
                refine ⟨4999604273997605840021771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13332278063993615573391389 4999604273997605840021771)
                ·
                  refine ⟨7499406410996408760032657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4999604273997605840021771 7499406410996408760032657)
                  ·
                    refine ⟨5624554808247306570024493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7499406410996408760032657 5624554808247306570024493)
                    ·
                      refine ⟨2109208053092739963759185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5624554808247306570024493 2109208053092739963759185)
                      ·
                        rfl

theorem cell23_4107668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_4107668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107668 prefixEnd_4107668 := by exact prefixLift 4107668
  have htrace : WordTrace (prefixWord ++ tailWord_4107668) baseStart_4107668 baseEnd_4107668 := by
    simpa [prefixWord, tailWord_4107668, baseEnd_4107668] using wordTrace_append hprefix tailTrace_4107668
  have hstable : (prefixWord ++ tailWord_4107668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107668).length < 2 ^ (prefixWord ++ tailWord_4107668).sum := by decide
  have hdescent : baseEnd_4107668 < baseStart_4107668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107724 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4107724 : Nat := 118140960795 + 4107724 * 2 ^ 59
def prefixEnd_4107724 : Nat := 4983230072969 + 3 ^ 40 * 4107724 * 2
def baseEnd_4107724 : Nat := 2109236808009391744658927

theorem tailTrace_4107724 : CollatzResearch.WordTrace tailWord_4107724 prefixEnd_4107724 2109236808009391744658927 := by
  unfold tailWord_4107724
  simp only [CollatzResearch.WordTrace]
  refine ⟨74910501285212483125793113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99880668380283310834390817 74910501285212483125793113)
  ·
    refine ⟨56182875963909362344344835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74910501285212483125793113 56182875963909362344344835)
    ·
      refine ⟨84274313945864043516517253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56182875963909362344344835 84274313945864043516517253)
      ·
        refine ⟨15801433864849508159346985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84274313945864043516517253 15801433864849508159346985)
        ·
          refine ⟨11851075398637131119510239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15801433864849508159346985 11851075398637131119510239)
          ·
            refine ⟨17776613097955696679265359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11851075398637131119510239 17776613097955696679265359)
            ·
              refine ⟨26664919646933545018898039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17776613097955696679265359 26664919646933545018898039)
              ·
                refine ⟨39997379470400317528347059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26664919646933545018898039 39997379470400317528347059)
                ·
                  refine ⟨59996069205600476292520589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39997379470400317528347059 59996069205600476292520589)
                  ·
                    refine ⟨22498525952100178609695221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59996069205600476292520589 22498525952100178609695221)
                    ·
                      refine ⟨2109236808009391744658927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22498525952100178609695221 2109236808009391744658927)
                      ·
                        rfl

theorem cell23_4107724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4107724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107724 prefixEnd_4107724 := by exact prefixLift 4107724
  have htrace : WordTrace (prefixWord ++ tailWord_4107724) baseStart_4107724 baseEnd_4107724 := by
    simpa [prefixWord, tailWord_4107724, baseEnd_4107724] using wordTrace_append hprefix tailTrace_4107724
  have hstable : (prefixWord ++ tailWord_4107724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107724).length < 2 ^ (prefixWord ++ tailWord_4107724).sum := by decide
  have hdescent : baseEnd_4107724 < baseStart_4107724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107727 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 9]
def baseStart_4107727 : Nat := 118140960795 + 4107727 * 2 ^ 59
def prefixEnd_4107727 : Nat := 4983230072969 + 3 ^ 40 * 4107727 * 2
def baseEnd_4107727 : Nat := 234359816494595025880157

theorem tailTrace_4107727 : CollatzResearch.WordTrace tailWord_4107727 prefixEnd_4107727 234359816494595025880157 := by
  unfold tailWord_4107727
  simp only [CollatzResearch.WordTrace]
  refine ⟨149821111989414097763945435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99880741326276065175963623 149821111989414097763945435)
  ·
    refine ⟨224731667984121146645918153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149821111989414097763945435 224731667984121146645918153)
    ·
      refine ⟨168548750988090859984438615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224731667984121146645918153 168548750988090859984438615)
      ·
        refine ⟨252823126482136289976657923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168548750988090859984438615 252823126482136289976657923)
        ·
          refine ⟨379234689723204434964986885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252823126482136289976657923 379234689723204434964986885)
          ·
            refine ⟨71106504323100831555935041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379234689723204434964986885 71106504323100831555935041)
            ·
              refine ⟨53329878242325623666951281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71106504323100831555935041 53329878242325623666951281)
              ·
                refine ⟨39997408681744217750213461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53329878242325623666951281 39997408681744217750213461)
                ·
                  refine ⟨234359816494595025880157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39997408681744217750213461 234359816494595025880157)
                  ·
                    rfl

theorem cell23_4107727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 9].length) (baseStart_4107727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107727 prefixEnd_4107727 := by exact prefixLift 4107727
  have htrace : WordTrace (prefixWord ++ tailWord_4107727) baseStart_4107727 baseEnd_4107727 := by
    simpa [prefixWord, tailWord_4107727, baseEnd_4107727] using wordTrace_append hprefix tailTrace_4107727
  have hstable : (prefixWord ++ tailWord_4107727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107727).length < 2 ^ (prefixWord ++ tailWord_4107727).sum := by decide
  have hdescent : baseEnd_4107727 < baseStart_4107727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107738 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2]
def baseStart_4107738 : Nat := 118140960795 + 4107738 * 2 ^ 59
def prefixEnd_4107738 : Nat := 4983230072969 + 3 ^ 40 * 4107738 * 2
def baseEnd_4107738 : Nat := 2109243996738554689883863

theorem tailTrace_4107738 : CollatzResearch.WordTrace tailWord_4107738 prefixEnd_4107738 2109243996738554689883863 := by
  unfold tailWord_4107738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37455378298093561660648967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99881008794916164428397245 37455378298093561660648967)
  ·
    refine ⟨56183067447140342490973451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37455378298093561660648967 56183067447140342490973451)
    ·
      refine ⟨84274601170710513736460177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56183067447140342490973451 84274601170710513736460177)
      ·
        refine ⟨63205950878032885302345133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84274601170710513736460177 63205950878032885302345133)
        ·
          refine ⟨23702231579262331988379425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63205950878032885302345133 23702231579262331988379425)
          ·
            refine ⟨17776673684446748991284569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23702231579262331988379425 17776673684446748991284569)
            ·
              refine ⟨13332505263335061743463427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17776673684446748991284569 13332505263335061743463427)
              ·
                refine ⟨19998757895002592615195141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13332505263335061743463427 19998757895002592615195141)
                ·
                  refine ⟨3749767105312986115349089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19998757895002592615195141 3749767105312986115349089)
                  ·
                    refine ⟨2812325328984739586511817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3749767105312986115349089 2812325328984739586511817)
                    ·
                      refine ⟨2109243996738554689883863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812325328984739586511817 2109243996738554689883863)
                      ·
                        rfl

theorem cell23_4107738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_4107738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107738 prefixEnd_4107738 := by exact prefixLift 4107738
  have htrace : WordTrace (prefixWord ++ tailWord_4107738) baseStart_4107738 baseEnd_4107738 := by
    simpa [prefixWord, tailWord_4107738, baseEnd_4107738] using wordTrace_append hprefix tailTrace_4107738
  have hstable : (prefixWord ++ tailWord_4107738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107738).length < 2 ^ (prefixWord ++ tailWord_4107738).sum := by decide
  have hdescent : baseEnd_4107738 < baseStart_4107738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107784 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_4107784 : Nat := 118140960795 + 4107784 * 2 ^ 59
def prefixEnd_4107784 : Nat := 4983230072969 + 3 ^ 40 * 4107784 * 2
def baseEnd_4107784 : Nat := 2109267616848661509908651

theorem tailTrace_4107784 : CollatzResearch.WordTrace tailWord_4107784 prefixEnd_4107784 2109267616848661509908651 := by
  unfold tailWord_4107784
  simp only [CollatzResearch.WordTrace]
  refine ⟨74911595475103798249385203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99882127300138397665846937 74911595475103798249385203)
  ·
    refine ⟨112367393212655697374077805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74911595475103798249385203 112367393212655697374077805)
    ·
      refine ⟨42137772454745886515279177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112367393212655697374077805 42137772454745886515279177)
      ·
        refine ⟨31603329341059414886459383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42137772454745886515279177 31603329341059414886459383)
        ·
          refine ⟨47404994011589122329689075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31603329341059414886459383 47404994011589122329689075)
          ·
            refine ⟨71107491017383683494533613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47404994011589122329689075 71107491017383683494533613)
            ·
              refine ⟨26665309131518881310450105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71107491017383683494533613 26665309131518881310450105)
              ·
                refine ⟨19998981848639160982837579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26665309131518881310450105 19998981848639160982837579)
                ·
                  refine ⟨29998472772958741474256369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19998981848639160982837579 29998472772958741474256369)
                  ·
                    refine ⟨22498854579719056105692277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29998472772958741474256369 22498854579719056105692277)
                    ·
                      refine ⟨2109267616848661509908651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22498854579719056105692277 2109267616848661509908651)
                      ·
                        rfl

theorem cell23_4107784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_4107784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107784 prefixEnd_4107784 := by exact prefixLift 4107784
  have htrace : WordTrace (prefixWord ++ tailWord_4107784) baseStart_4107784 baseEnd_4107784 := by
    simpa [prefixWord, tailWord_4107784, baseEnd_4107784] using wordTrace_append hprefix tailTrace_4107784
  have hstable : (prefixWord ++ tailWord_4107784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107784).length < 2 ^ (prefixWord ++ tailWord_4107784).sum := by decide
  have hdescent : baseEnd_4107784 < baseStart_4107784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107831 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_4107831 : Nat := 118140960795 + 4107831 * 2 ^ 59
def prefixEnd_4107831 : Nat := 4983230072969 + 3 ^ 40 * 4107831 * 2
def baseEnd_4107831 : Nat := 2109291750439422826020935

theorem tailTrace_4107831 : CollatzResearch.WordTrace tailWord_4107831 prefixEnd_4107831 2109291750439422826020935 := by
  unfold tailWord_4107831
  simp only [CollatzResearch.WordTrace]
  refine ⟨149824905181037323525731347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99883270120691549017154231 149824905181037323525731347)
  ·
    refine ⟨224737357771555985288597021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149824905181037323525731347 224737357771555985288597021)
    ·
      refine ⟨84276509164333494483223883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224737357771555985288597021 84276509164333494483223883)
      ·
        refine ⟨126414763746500241724835825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84276509164333494483223883 126414763746500241724835825)
        ·
          refine ⟨94811072809875181293626869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126414763746500241724835825 94811072809875181293626869)
          ·
            refine ⟨8888538075925798246277519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94811072809875181293626869 8888538075925798246277519)
            ·
              refine ⟨13332807113888697369416279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8888538075925798246277519 13332807113888697369416279)
              ·
                refine ⟨19999210670833046054124419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13332807113888697369416279 19999210670833046054124419)
                ·
                  refine ⟨29998816006249569081186629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19999210670833046054124419 29998816006249569081186629)
                  ·
                    refine ⟨5624778001171794202722493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29998816006249569081186629 5624778001171794202722493)
                    ·
                      refine ⟨2109291750439422826020935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5624778001171794202722493 2109291750439422826020935)
                      ·
                        rfl

theorem cell23_4107831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_4107831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107831 prefixEnd_4107831 := by exact prefixLift 4107831
  have htrace : WordTrace (prefixWord ++ tailWord_4107831) baseStart_4107831 baseEnd_4107831 := by
    simpa [prefixWord, tailWord_4107831, baseEnd_4107831] using wordTrace_append hprefix tailTrace_4107831
  have hstable : (prefixWord ++ tailWord_4107831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107831).length < 2 ^ (prefixWord ++ tailWord_4107831).sum := by decide
  have hdescent : baseEnd_4107831 < baseStart_4107831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107834 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 8]
def baseStart_4107834 : Nat := 118140960795 + 4107834 * 2 ^ 59
def prefixEnd_4107834 : Nat := 4983230072969 + 3 ^ 40 * 4107834 * 2
def baseEnd_4107834 : Nat := 234365921209042923809269

theorem tailTrace_4107834 : CollatzResearch.WordTrace tailWord_4107834 prefixEnd_4107834 234365921209042923809269 := by
  unfold tailWord_4107834
  simp only [CollatzResearch.WordTrace]
  refine ⟨37456253650006613759522639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99883343066684303358727037 37456253650006613759522639)
  ·
    refine ⟨56184380475009920639283959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37456253650006613759522639 56184380475009920639283959)
    ·
      refine ⟨84276570712514880958925939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56184380475009920639283959 84276570712514880958925939)
      ·
        refine ⟨126414856068772321438388909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84276570712514880958925939 126414856068772321438388909)
        ·
          refine ⟨47405571025789620539395841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126414856068772321438388909 47405571025789620539395841)
          ·
            refine ⟨35554178269342215404546881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47405571025789620539395841 35554178269342215404546881)
            ·
              refine ⟨26665633702006661553410161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35554178269342215404546881 26665633702006661553410161)
              ·
                refine ⟨19999225276504996165057621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26665633702006661553410161 19999225276504996165057621)
                ·
                  refine ⟨234365921209042923809269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19999225276504996165057621 234365921209042923809269)
                  ·
                    rfl

theorem cell23_4107834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_4107834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107834 prefixEnd_4107834 := by exact prefixLift 4107834
  have htrace : WordTrace (prefixWord ++ tailWord_4107834) baseStart_4107834 baseEnd_4107834 := by
    simpa [prefixWord, tailWord_4107834, baseEnd_4107834] using wordTrace_append hprefix tailTrace_4107834
  have hstable : (prefixWord ++ tailWord_4107834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107834).length < 2 ^ (prefixWord ++ tailWord_4107834).sum := by decide
  have hdescent : baseEnd_4107834 < baseStart_4107834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107881 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 1, 5]
def baseStart_4107881 : Nat := 118140960795 + 4107881 * 2 ^ 59
def prefixEnd_4107881 : Nat := 4983230072969 + 3 ^ 40 * 4107881 * 2
def baseEnd_4107881 : Nat := 703105808157382543465235

theorem tailTrace_4107881 : CollatzResearch.WordTrace tailWord_4107881 prefixEnd_4107881 703105808157382543465235 := by
  unfold tailWord_4107881
  simp only [CollatzResearch.WordTrace]
  refine ⟨149826728830856182065051497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99884485887237454710034331 149826728830856182065051497)
  ·
    refine ⟨112370046623142136548788623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149826728830856182065051497 112370046623142136548788623)
    ·
      refine ⟨168555069934713204823182935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112370046623142136548788623 168555069934713204823182935)
      ·
        refine ⟨252832604902069807234774403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168555069934713204823182935 252832604902069807234774403)
        ·
          refine ⟨379248907353104710852161605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252832604902069807234774403 379248907353104710852161605)
          ·
            refine ⟨71109170128707133284780301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379248907353104710852161605 71109170128707133284780301)
            ·
              refine ⟨26665938798265174981792613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71109170128707133284780301 26665938798265174981792613)
              ·
                refine ⟨4999863524674720309086115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26665938798265174981792613 4999863524674720309086115)
                ·
                  refine ⟨7499795287012080463629173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4999863524674720309086115 7499795287012080463629173)
                  ·
                    refine ⟨703105808157382543465235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7499795287012080463629173 703105808157382543465235)
                    ·
                      rfl

theorem cell23_4107881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 5].length) (baseStart_4107881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107881 prefixEnd_4107881 := by exact prefixLift 4107881
  have htrace : WordTrace (prefixWord ++ tailWord_4107881) baseStart_4107881 baseEnd_4107881 := by
    simpa [prefixWord, tailWord_4107881, baseEnd_4107881] using wordTrace_append hprefix tailTrace_4107881
  have hstable : (prefixWord ++ tailWord_4107881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107881).length < 2 ^ (prefixWord ++ tailWord_4107881).sum := by decide
  have hdescent : baseEnd_4107881 < baseStart_4107881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107888 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 1, 5, 2]
def baseStart_4107888 : Nat := 118140960795 + 4107888 * 2 ^ 59
def prefixEnd_4107888 : Nat := 4983230072969 + 3 ^ 40 * 4107888 * 2
def baseEnd_4107888 : Nat := 2109321018836729103008173

theorem tailTrace_4107888 : CollatzResearch.WordTrace tailWord_4107888 prefixEnd_4107888 2109321018836729103008173 := by
  unfold tailWord_4107888
  simp only [CollatzResearch.WordTrace]
  refine ⟨74913492070915411130278159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99884656094553881507037545 74913492070915411130278159)
  ·
    refine ⟨112370238106373116695417239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74913492070915411130278159 112370238106373116695417239)
    ·
      refine ⟨168555357159559675043125859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112370238106373116695417239 168555357159559675043125859)
      ·
        refine ⟨252833035739339512564688789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168555357159559675043125859 252833035739339512564688789)
        ·
          refine ⟨11851548550281539651469787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 252833035739339512564688789 11851548550281539651469787)
          ·
            refine ⟨17777322825422309477204681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11851548550281539651469787 17777322825422309477204681)
            ·
              refine ⟨13332992119066732107903511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17777322825422309477204681 13332992119066732107903511)
              ·
                refine ⟨19999488178600098161855267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13332992119066732107903511 19999488178600098161855267)
                ·
                  refine ⟨29999232267900147242782901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19999488178600098161855267 29999232267900147242782901)
                  ·
                    refine ⟨2812428025115638804010897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29999232267900147242782901 2812428025115638804010897)
                    ·
                      refine ⟨2109321018836729103008173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812428025115638804010897 2109321018836729103008173)
                      ·
                        rfl

theorem cell23_4107888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 5, 2].length) (baseStart_4107888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107888 prefixEnd_4107888 := by exact prefixLift 4107888
  have htrace : WordTrace (prefixWord ++ tailWord_4107888) baseStart_4107888 baseEnd_4107888 := by
    simpa [prefixWord, tailWord_4107888, baseEnd_4107888] using wordTrace_append hprefix tailTrace_4107888
  have hstable : (prefixWord ++ tailWord_4107888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107888).length < 2 ^ (prefixWord ++ tailWord_4107888).sum := by decide
  have hdescent : baseEnd_4107888 < baseStart_4107888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107905 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_4107905 : Nat := 118140960795 + 4107905 * 2 ^ 59
def prefixEnd_4107905 : Nat := 4983230072969 + 3 ^ 40 * 4107905 * 2
def baseEnd_4107905 : Nat := 2109329748007855536495595

theorem tailTrace_4107905 : CollatzResearch.WordTrace tailWord_4107905 prefixEnd_4107905 2109329748007855536495595 := by
  unfold tailWord_4107905
  simp only [CollatzResearch.WordTrace]
  refine ⟨149827604182769234163925169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99885069455179489442616779 149827604182769234163925169)
  ·
    refine ⟨112370703137076925622943877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149827604182769234163925169 112370703137076925622943877)
    ·
      refine ⟨21069506838201923554301977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112370703137076925622943877 21069506838201923554301977)
      ·
        refine ⟨15802130128651442665726483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21069506838201923554301977 15802130128651442665726483)
        ·
          refine ⟨23703195192977163998589725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15802130128651442665726483 23703195192977163998589725)
          ·
            refine ⟨8888698197366436499471147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23703195192977163998589725 8888698197366436499471147)
            ·
              refine ⟨13333047296049654749206721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8888698197366436499471147 13333047296049654749206721)
              ·
                refine ⟨9999785472037241061905041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13333047296049654749206721 9999785472037241061905041)
                ·
                  refine ⟨7499839104027930796428781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9999785472037241061905041 7499839104027930796428781)
                  ·
                    refine ⟨2812439664010474048660793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7499839104027930796428781 2812439664010474048660793)
                    ·
                      refine ⟨2109329748007855536495595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812439664010474048660793 2109329748007855536495595)
                      ·
                        rfl

theorem cell23_4107905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_4107905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107905 prefixEnd_4107905 := by exact prefixLift 4107905
  have htrace : WordTrace (prefixWord ++ tailWord_4107905) baseStart_4107905 baseEnd_4107905 := by
    simpa [prefixWord, tailWord_4107905, baseEnd_4107905] using wordTrace_append hprefix tailTrace_4107905
  have hstable : (prefixWord ++ tailWord_4107905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107905).length < 2 ^ (prefixWord ++ tailWord_4107905).sum := by decide
  have hdescent : baseEnd_4107905 < baseStart_4107905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107932 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_4107932 : Nat := 118140960795 + 4107932 * 2 ^ 59
def prefixEnd_4107932 : Nat := 4983230072969 + 3 ^ 40 * 4107932 * 2
def baseEnd_4107932 : Nat := 703114537328508976952657

theorem tailTrace_4107932 : CollatzResearch.WordTrace tailWord_4107932 prefixEnd_4107932 703114537328508976952657 := by
  unfold tailWord_4107932
  simp only [CollatzResearch.WordTrace]
  refine ⟨74914294476835708887579025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99885725969114278516772033 74914294476835708887579025)
  ·
    refine ⟨56185720857626781665684269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74914294476835708887579025 56185720857626781665684269)
    ·
      refine ⟨21069645321610043124631601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56185720857626781665684269 21069645321610043124631601)
      ·
        refine ⟨15802233991207532343473701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21069645321610043124631601 15802233991207532343473701)
        ·
          refine ⟨2962918873351412314401319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15802233991207532343473701 2962918873351412314401319)
          ·
            refine ⟨4444378310027118471601979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962918873351412314401319 4444378310027118471601979)
            ·
              refine ⟨6666567465040677707402969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444378310027118471601979 6666567465040677707402969)
              ·
                refine ⟨4999925598780508280552227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6666567465040677707402969 4999925598780508280552227)
                ·
                  refine ⟨7499888398170762420828341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4999925598780508280552227 7499888398170762420828341)
                  ·
                    refine ⟨703114537328508976952657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7499888398170762420828341 703114537328508976952657)
                    ·
                      rfl

theorem cell23_4107932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_4107932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107932 prefixEnd_4107932 := by exact prefixLift 4107932
  have htrace : WordTrace (prefixWord ++ tailWord_4107932) baseStart_4107932 baseEnd_4107932 := by
    simpa [prefixWord, tailWord_4107932, baseEnd_4107932] using wordTrace_append hprefix tailTrace_4107932
  have hstable : (prefixWord ++ tailWord_4107932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107932).length < 2 ^ (prefixWord ++ tailWord_4107932).sum := by decide
  have hdescent : baseEnd_4107932 < baseStart_4107932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107935 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4107935 : Nat := 118140960795 + 4107935 * 2 ^ 59
def prefixEnd_4107935 : Nat := 4983230072969 + 3 ^ 40 * 4107935 * 2
def baseEnd_4107935 : Nat := 2109345152427490419120457

theorem tailTrace_4107935 : CollatzResearch.WordTrace tailWord_4107935 prefixEnd_4107935 2109345152427490419120457 := by
  unfold tailWord_4107935
  simp only [CollatzResearch.WordTrace]
  refine ⟨149828698372660549287517259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99885798915107032858344839 149828698372660549287517259)
  ·
    refine ⟨224743047558990823931275889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149828698372660549287517259 224743047558990823931275889)
    ·
      refine ⟨168557285669243117948456917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224743047558990823931275889 168557285669243117948456917)
      ·
        refine ⟨3950561382872885576916959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 168557285669243117948456917 3950561382872885576916959)
        ·
          refine ⟨5925842074309328365375439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950561382872885576916959 5925842074309328365375439)
          ·
            refine ⟨8888763111463992548063159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5925842074309328365375439 8888763111463992548063159)
            ·
              refine ⟨13333144667195988822094739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8888763111463992548063159 13333144667195988822094739)
              ·
                refine ⟨19999717000793983233142109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13333144667195988822094739 19999717000793983233142109)
                ·
                  refine ⟨7499893875297743712428291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19999717000793983233142109 7499893875297743712428291)
                  ·
                    refine ⟨11249840812946615568642437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7499893875297743712428291 11249840812946615568642437)
                    ·
                      refine ⟨2109345152427490419120457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11249840812946615568642437 2109345152427490419120457)
                      ·
                        rfl

theorem cell23_4107935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4107935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107935 prefixEnd_4107935 := by exact prefixLift 4107935
  have htrace : WordTrace (prefixWord ++ tailWord_4107935) baseStart_4107935 baseEnd_4107935 := by
    simpa [prefixWord, tailWord_4107935, baseEnd_4107935] using wordTrace_append hprefix tailTrace_4107935
  have hstable : (prefixWord ++ tailWord_4107935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107935).length < 2 ^ (prefixWord ++ tailWord_4107935).sum := by decide
  have hdescent : baseEnd_4107935 < baseStart_4107935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107955 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 1, 2, 3]
def baseStart_4107955 : Nat := 118140960795 + 4107955 * 2 ^ 59
def prefixEnd_4107955 : Nat := 4983230072969 + 3 ^ 40 * 4107955 * 2
def baseEnd_4107955 : Nat := 2109355422040580340870365

theorem tailTrace_4107955 : CollatzResearch.WordTrace tailWord_4107955 prefixEnd_4107955 2109355422040580340870365 := by
  unfold tailWord_4107955
  simp only [CollatzResearch.WordTrace]
  refine ⟨149829427832588092703245319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99886285221725395135496879 149829427832588092703245319)
  ·
    refine ⟨224744141748882139054867979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149829427832588092703245319 224744141748882139054867979)
    ·
      refine ⟨337116212623323208582301969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224744141748882139054867979 337116212623323208582301969)
      ·
        refine ⟨252837159467492406436726477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337116212623323208582301969 252837159467492406436726477)
        ·
          refine ⟨94813934800309652413772429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252837159467492406436726477 94813934800309652413772429)
          ·
            refine ⟨35555225550116119655164661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94813934800309652413772429 35555225550116119655164661)
            ·
              refine ⟨3333302395323386217671687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35555225550116119655164661 3333302395323386217671687)
              ·
                refine ⟨4999953592985079326507531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333302395323386217671687 4999953592985079326507531)
                ·
                  refine ⟨7499930389477618989761297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4999953592985079326507531 7499930389477618989761297)
                  ·
                    refine ⟨5624947792108214242320973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7499930389477618989761297 5624947792108214242320973)
                    ·
                      refine ⟨2109355422040580340870365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5624947792108214242320973 2109355422040580340870365)
                      ·
                        rfl

theorem cell23_4107955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 2, 3].length) (baseStart_4107955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107955 prefixEnd_4107955 := by exact prefixLift 4107955
  have htrace : WordTrace (prefixWord ++ tailWord_4107955) baseStart_4107955 baseEnd_4107955 := by
    simpa [prefixWord, tailWord_4107955, baseEnd_4107955] using wordTrace_append hprefix tailTrace_4107955
  have hstable : (prefixWord ++ tailWord_4107955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107955).length < 2 ^ (prefixWord ++ tailWord_4107955).sum := by decide
  have hdescent : baseEnd_4107955 < baseStart_4107955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107958 : List Nat := [5, 1, 3, 1, 1, 12]
def baseStart_4107958 : Nat := 118140960795 + 4107958 * 2 ^ 59
def prefixEnd_4107958 : Nat := 4983230072969 + 3 ^ 40 * 4107958 * 2
def baseEnd_4107958 : Nat := 8680481327088657733057

theorem tailTrace_4107958 : CollatzResearch.WordTrace tailWord_4107958 prefixEnd_4107958 8680481327088657733057 := by
  unfold tailWord_4107958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364346078223576513475283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99886358167718149477069685 9364346078223576513475283)
  ·
    refine ⟨14046519117335364770212925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9364346078223576513475283 14046519117335364770212925)
    ·
      refine ⟨5267444669000761788829847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14046519117335364770212925 5267444669000761788829847)
      ·
        refine ⟨7901167003501142683244771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5267444669000761788829847 7901167003501142683244771)
        ·
          refine ⟨11851750505251714024867157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7901167003501142683244771 11851750505251714024867157)
          ·
            refine ⟨8680481327088657733057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11851750505251714024867157 8680481327088657733057)
            ·
              rfl

theorem cell23_4107958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 12].length) (baseStart_4107958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107958 prefixEnd_4107958 := by exact prefixLift 4107958
  have htrace : WordTrace (prefixWord ++ tailWord_4107958) baseStart_4107958 baseEnd_4107958 := by
    simpa [prefixWord, tailWord_4107958, baseEnd_4107958] using wordTrace_append hprefix tailTrace_4107958
  have hstable : (prefixWord ++ tailWord_4107958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107958).length < 2 ^ (prefixWord ++ tailWord_4107958).sum := by decide
  have hdescent : baseEnd_4107958 < baseStart_4107958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107985 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 3]
def baseStart_4107985 : Nat := 118140960795 + 4107985 * 2 ^ 59
def prefixEnd_4107985 : Nat := 4983230072969 + 3 ^ 40 * 4107985 * 2
def baseEnd_4107985 : Nat := 2109370826460215223495227

theorem tailTrace_4107985 : CollatzResearch.WordTrace tailWord_4107985 prefixEnd_4107985 2109370826460215223495227 := by
  unfold tailWord_4107985
  simp only [CollatzResearch.WordTrace]
  refine ⟨149830522022479407826837409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99887014681652938551224939 149830522022479407826837409)
  ·
    refine ⟨112372891516859555870128057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149830522022479407826837409 112372891516859555870128057)
    ·
      refine ⟨84279668637644666902596043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112372891516859555870128057 84279668637644666902596043)
      ·
        refine ⟨126419502956467000353894065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84279668637644666902596043 126419502956467000353894065)
        ·
          refine ⟨94814627217350250265420549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126419502956467000353894065 94814627217350250265420549)
          ·
            refine ⟨17777742603253171924766353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94814627217350250265420549 17777742603253171924766353)
            ·
              refine ⟨13333306952439878943574765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17777742603253171924766353 13333306952439878943574765)
              ·
                refine ⟨4999990107164954603840537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13333306952439878943574765 4999990107164954603840537)
                ·
                  refine ⟨3749992580373715952880403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4999990107164954603840537 3749992580373715952880403)
                  ·
                    refine ⟨5624988870560573929320605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3749992580373715952880403 5624988870560573929320605)
                    ·
                      refine ⟨2109370826460215223495227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5624988870560573929320605 2109370826460215223495227)
                      ·
                        rfl

theorem cell23_4107985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_4107985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107985 prefixEnd_4107985 := by exact prefixLift 4107985
  have htrace : WordTrace (prefixWord ++ tailWord_4107985) baseStart_4107985 baseEnd_4107985 := by
    simpa [prefixWord, tailWord_4107985, baseEnd_4107985] using wordTrace_append hprefix tailTrace_4107985
  have hstable : (prefixWord ++ tailWord_4107985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107985).length < 2 ^ (prefixWord ++ tailWord_4107985).sum := by decide
  have hdescent : baseEnd_4107985 < baseStart_4107985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107991 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_4107991 : Nat := 118140960795 + 4107991 * 2 ^ 59
def prefixEnd_4107991 : Nat := 4983230072969 + 3 ^ 40 * 4107991 * 2
def baseEnd_4107991 : Nat := 2109373907344142200020199

theorem tailTrace_4107991 : CollatzResearch.WordTrace tailWord_4107991 prefixEnd_4107991 2109373907344142200020199 := by
  unfold tailWord_4107991
  simp only [CollatzResearch.WordTrace]
  refine ⟨149830740860457670851555827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99887160573638447234370551 149830740860457670851555827)
  ·
    refine ⟨224746111290686506277333741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149830740860457670851555827 224746111290686506277333741)
    ·
      refine ⟨84279791734007439854000153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224746111290686506277333741 84279791734007439854000153)
      ·
        refine ⟨63209843800505579890500115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84279791734007439854000153 63209843800505579890500115)
        ·
          refine ⟨94814765700758369835750173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63209843800505579890500115 94814765700758369835750173)
          ·
            refine ⟨35555537137784388688406315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94814765700758369835750173 35555537137784388688406315)
            ·
              refine ⟨53333305706676583032609473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35555537137784388688406315 53333305706676583032609473)
              ·
                refine ⟨39999979280007437274457105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53333305706676583032609473 39999979280007437274457105)
                ·
                  refine ⟨29999984460005577955842829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39999979280007437274457105 29999984460005577955842829)
                  ·
                    refine ⟨11249994172502091733441061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29999984460005577955842829 11249994172502091733441061)
                    ·
                      refine ⟨2109373907344142200020199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11249994172502091733441061 2109373907344142200020199)
                      ·
                        rfl

theorem cell23_4107991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_4107991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4107991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4107991 prefixEnd_4107991 := by exact prefixLift 4107991
  have htrace : WordTrace (prefixWord ++ tailWord_4107991) baseStart_4107991 baseEnd_4107991 := by
    simpa [prefixWord, tailWord_4107991, baseEnd_4107991] using wordTrace_append hprefix tailTrace_4107991
  have hstable : (prefixWord ++ tailWord_4107991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107991).length < 2 ^ (prefixWord ++ tailWord_4107991).sum := by decide
  have hdescent : baseEnd_4107991 < baseStart_4107991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108011 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 5]
def baseStart_4108011 : Nat := 118140960795 + 4108011 * 2 ^ 59
def prefixEnd_4108011 : Nat := 4983230072969 + 3 ^ 40 * 4108011 * 2
def baseEnd_4108011 : Nat := 2109384176957232121770107

theorem tailTrace_4108011 : CollatzResearch.WordTrace tailWord_4108011 prefixEnd_4108011 2109384176957232121770107 := by
  unfold tailWord_4108011
  simp only [CollatzResearch.WordTrace]
  refine ⟨149831470320385214267283887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99887646880256809511522591 149831470320385214267283887)
  ·
    refine ⟨224747205480577821400925831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149831470320385214267283887 224747205480577821400925831)
    ·
      refine ⟨337120808220866732101388747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224747205480577821400925831 337120808220866732101388747)
      ·
        refine ⟨505681212331300098152083121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337120808220866732101388747 505681212331300098152083121)
        ·
          refine ⟨379260909248475073614062341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505681212331300098152083121 379260909248475073614062341)
          ·
            refine ⟨71111420484089076302636689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379260909248475073614062341 71111420484089076302636689)
            ·
              refine ⟨53333565363066807226977517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71111420484089076302636689 53333565363066807226977517)
              ·
                refine ⟨20000087011150052710116569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53333565363066807226977517 20000087011150052710116569)
                ·
                  refine ⟨15000065258362539532587427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20000087011150052710116569 15000065258362539532587427)
                  ·
                    refine ⟨22500097887543809298881141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15000065258362539532587427 22500097887543809298881141)
                    ·
                      refine ⟨2109384176957232121770107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22500097887543809298881141 2109384176957232121770107)
                      ·
                        rfl

theorem cell23_4108011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 5].length) (baseStart_4108011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108011 prefixEnd_4108011 := by exact prefixLift 4108011
  have htrace : WordTrace (prefixWord ++ tailWord_4108011) baseStart_4108011 baseEnd_4108011 := by
    simpa [prefixWord, tailWord_4108011, baseEnd_4108011] using wordTrace_append hprefix tailTrace_4108011
  have hstable : (prefixWord ++ tailWord_4108011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108011).length < 2 ^ (prefixWord ++ tailWord_4108011).sum := by decide
  have hdescent : baseEnd_4108011 < baseStart_4108011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108012 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 1, 3, 2]
def baseStart_4108012 : Nat := 118140960795 + 4108012 * 2 ^ 59
def prefixEnd_4108012 : Nat := 4983230072969 + 3 ^ 40 * 4108012 * 2
def baseEnd_4108012 : Nat := 2109384690437886617857603

theorem tailTrace_4108012 : CollatzResearch.WordTrace tailWord_4108012 prefixEnd_4108012 2109384690437886617857603 := by
  unfold tailWord_4108012
  simp only [CollatzResearch.WordTrace]
  refine ⟨74915753396690795719035145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99887671195587727625380193 74915753396690795719035145)
  ·
    refine ⟨56186815047518096789276359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74915753396690795719035145 56186815047518096789276359)
    ·
      refine ⟨84280222571277145183914539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56186815047518096789276359 84280222571277145183914539)
      ·
        refine ⟨126420333856915717775871809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84280222571277145183914539 126420333856915717775871809)
        ·
          refine ⟨94815250392686788331903857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126420333856915717775871809 94815250392686788331903857)
          ·
            refine ⟨71111437794515091248927893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94815250392686788331903857 71111437794515091248927893)
            ·
              refine ⟨3333348646617894902293495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71111437794515091248927893 3333348646617894902293495)
              ·
                refine ⟨5000022969926842353440243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333348646617894902293495 5000022969926842353440243)
                ·
                  refine ⟨7500034454890263530160365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000022969926842353440243 7500034454890263530160365)
                  ·
                    refine ⟨2812512920583848823810137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7500034454890263530160365 2812512920583848823810137)
                    ·
                      refine ⟨2109384690437886617857603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812512920583848823810137 2109384690437886617857603)
                      ·
                        rfl

theorem cell23_4108012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_4108012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108012 prefixEnd_4108012 := by exact prefixLift 4108012
  have htrace : WordTrace (prefixWord ++ tailWord_4108012) baseStart_4108012 baseEnd_4108012 := by
    simpa [prefixWord, tailWord_4108012, baseEnd_4108012] using wordTrace_append hprefix tailTrace_4108012
  have hstable : (prefixWord ++ tailWord_4108012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108012).length < 2 ^ (prefixWord ++ tailWord_4108012).sum := by decide
  have hdescent : baseEnd_4108012 < baseStart_4108012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108031 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 7]
def baseStart_4108031 : Nat := 118140960795 + 4108031 * 2 ^ 59
def prefixEnd_4108031 : Nat := 4983230072969 + 3 ^ 40 * 4108031 * 2
def baseEnd_4108031 : Nat := 234377160730035782613335

theorem tailTrace_4108031 : CollatzResearch.WordTrace tailWord_4108031 prefixEnd_4108031 234377160730035782613335 := by
  unfold tailWord_4108031
  simp only [CollatzResearch.WordTrace]
  refine ⟨149832199780312757683011947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99888133186875171788674631 149832199780312757683011947)
  ·
    refine ⟨224748299670469136524517921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149832199780312757683011947 224748299670469136524517921)
    ·
      refine ⟨168561224752851852393388441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224748299670469136524517921 168561224752851852393388441)
      ·
        refine ⟨126420918564638889295041331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168561224752851852393388441 126420918564638889295041331)
        ·
          refine ⟨189631377846958333942561997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126420918564638889295041331 189631377846958333942561997)
          ·
            refine ⟨71111766692609375228460749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189631377846958333942561997 71111766692609375228460749)
            ·
              refine ⟨26666912509728515710672781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71111766692609375228460749 26666912509728515710672781)
              ·
                refine ⟨10000092191148193391502293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26666912509728515710672781 10000092191148193391502293)
                ·
                  refine ⟨234377160730035782613335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10000092191148193391502293 234377160730035782613335)
                  ·
                    rfl

theorem cell23_4108031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 7].length) (baseStart_4108031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108031 prefixEnd_4108031 := by exact prefixLift 4108031
  have htrace : WordTrace (prefixWord ++ tailWord_4108031) baseStart_4108031 baseEnd_4108031 := by
    simpa [prefixWord, tailWord_4108031, baseEnd_4108031] using wordTrace_append hprefix tailTrace_4108031
  have hstable : (prefixWord ++ tailWord_4108031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108031).length < 2 ^ (prefixWord ++ tailWord_4108031).sum := by decide
  have hdescent : baseEnd_4108031 < baseStart_4108031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108042 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_4108042 : Nat := 118140960795 + 4108042 * 2 ^ 59
def prefixEnd_4108042 : Nat := 4983230072969 + 3 ^ 40 * 4108042 * 2
def baseEnd_4108042 : Nat := 2109400094857521500482465

theorem tailTrace_4108042 : CollatzResearch.WordTrace tailWord_4108042 prefixEnd_4108042 2109400094857521500482465 := by
  unfold tailWord_4108042
  simp only [CollatzResearch.WordTrace]
  refine ⟨37458150245818226640415595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99888400655515271041108253 37458150245818226640415595)
  ·
    refine ⟨56187225368727339960623393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37458150245818226640415595 56187225368727339960623393)
    ·
      refine ⟨42140419026545504970467545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56187225368727339960623393 42140419026545504970467545)
      ·
        refine ⟨31605314269909128727850659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42140419026545504970467545 31605314269909128727850659)
        ·
          refine ⟨47407971404863693091775989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31605314269909128727850659 47407971404863693091775989)
          ·
            refine ⟨4444497319205971227353999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47407971404863693091775989 4444497319205971227353999)
            ·
              refine ⟨6666745978808956841030999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444497319205971227353999 6666745978808956841030999)
              ·
                refine ⟨10000118968213435261546499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6666745978808956841030999 10000118968213435261546499)
                ·
                  refine ⟨15000178452320152892319749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10000118968213435261546499 15000178452320152892319749)
                  ·
                    refine ⟨2812533459810028667309953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15000178452320152892319749 2812533459810028667309953)
                    ·
                      refine ⟨2109400094857521500482465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812533459810028667309953 2109400094857521500482465)
                      ·
                        rfl

theorem cell23_4108042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_4108042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108042 prefixEnd_4108042 := by exact prefixLift 4108042
  have htrace : WordTrace (prefixWord ++ tailWord_4108042) baseStart_4108042 baseEnd_4108042 := by
    simpa [prefixWord, tailWord_4108042, baseEnd_4108042] using wordTrace_append hprefix tailTrace_4108042
  have hstable : (prefixWord ++ tailWord_4108042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108042).length < 2 ^ (prefixWord ++ tailWord_4108042).sum := by decide
  have hdescent : baseEnd_4108042 < baseStart_4108042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108065 : List Nat := [1, 2, 3, 2, 1, 3, 3, 3, 5]
def baseStart_4108065 : Nat := 118140960795 + 4108065 * 2 ^ 59
def prefixEnd_4108065 : Nat := 4983230072969 + 3 ^ 40 * 4108065 * 2
def baseEnd_4108065 : Nat := 234379100545841656721651

theorem tailTrace_4108065 : CollatzResearch.WordTrace tailWord_4108065 prefixEnd_4108065 234379100545841656721651 := by
  unfold tailWord_4108065
  simp only [CollatzResearch.WordTrace]
  refine ⟨149833439862189581489749649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99888959908126387659833099 149833439862189581489749649)
  ·
    refine ⟨112375079896642186117312237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149833439862189581489749649 112375079896642186117312237)
    ·
      refine ⟨42140654961240819793992089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112375079896642186117312237 42140654961240819793992089)
      ·
        refine ⟨31605491220930614845494067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42140654961240819793992089 31605491220930614845494067)
        ·
          refine ⟨47408236831395922268241101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31605491220930614845494067 47408236831395922268241101)
          ·
            refine ⟨17778088811773470850590413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47408236831395922268241101 17778088811773470850590413)
            ·
              refine ⟨6666783304415051568971405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17778088811773470850590413 6666783304415051568971405)
              ·
                refine ⟨2500043739155644338364277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6666783304415051568971405 2500043739155644338364277)
                ·
                  refine ⟨234379100545841656721651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2500043739155644338364277 234379100545841656721651)
                  ·
                    rfl

theorem cell23_4108065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 5].length) (baseStart_4108065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108065 prefixEnd_4108065 := by exact prefixLift 4108065
  have htrace : WordTrace (prefixWord ++ tailWord_4108065) baseStart_4108065 baseEnd_4108065 := by
    simpa [prefixWord, tailWord_4108065, baseEnd_4108065] using wordTrace_append hprefix tailTrace_4108065
  have hstable : (prefixWord ++ tailWord_4108065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108065).length < 2 ^ (prefixWord ++ tailWord_4108065).sum := by decide
  have hdescent : baseEnd_4108065 < baseStart_4108065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108082 : List Nat := [3, 2, 1, 1, 3, 3, 3, 2, 5]
def baseStart_4108082 : Nat := 118140960795 + 4108082 * 2 ^ 59
def prefixEnd_4108082 : Nat := 4983230072969 + 3 ^ 40 * 4108082 * 2
def baseEnd_4108082 : Nat := 234380070453744593775809

theorem tailTrace_4108082 : CollatzResearch.WordTrace tailWord_4108082 prefixEnd_4108082 234380070453744593775809 := by
  unfold tailWord_4108082
  simp only [CollatzResearch.WordTrace]
  refine ⟨37458514975781998348279625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99889373268751995595412333 37458514975781998348279625)
  ·
    refine ⟨28093886231836498761209719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37458514975781998348279625 28093886231836498761209719)
    ·
      refine ⟨42140829347754748141814579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28093886231836498761209719 42140829347754748141814579)
      ·
        refine ⟨63211244021632122212721869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42140829347754748141814579 63211244021632122212721869)
        ·
          refine ⟨23704216508112045829770701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63211244021632122212721869 23704216508112045829770701)
          ·
            refine ⟨8889081190542017186164013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23704216508112045829770701 8889081190542017186164013)
            ·
              refine ⟨3333405446453256444811505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8889081190542017186164013 3333405446453256444811505)
              ·
                refine ⟨2500054084839942333608629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333405446453256444811505 2500054084839942333608629)
                ·
                  refine ⟨234380070453744593775809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2500054084839942333608629 234380070453744593775809)
                  ·
                    rfl

theorem cell23_4108082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_4108082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108082 prefixEnd_4108082 := by exact prefixLift 4108082
  have htrace : WordTrace (prefixWord ++ tailWord_4108082) baseStart_4108082 baseEnd_4108082 := by
    simpa [prefixWord, tailWord_4108082, baseEnd_4108082] using wordTrace_append hprefix tailTrace_4108082
  have hstable : (prefixWord ++ tailWord_4108082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108082).length < 2 ^ (prefixWord ++ tailWord_4108082).sum := by decide
  have hdescent : baseEnd_4108082 < baseStart_4108082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108088 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_4108088 : Nat := 118140960795 + 4108088 * 2 ^ 59
def prefixEnd_4108088 : Nat := 4983230072969 + 3 ^ 40 * 4108088 * 2
def baseEnd_4108088 : Nat := 2109423714967628320507253

theorem tailTrace_4108088 : CollatzResearch.WordTrace tailWord_4108088 prefixEnd_4108088 2109423714967628320507253 := by
  unfold tailWord_4108088
  simp only [CollatzResearch.WordTrace]
  refine ⟨74917139370553128208918459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99889519160737504278557945 74917139370553128208918459)
  ·
    refine ⟨112375709055829692313377689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74917139370553128208918459 112375709055829692313377689)
    ·
      refine ⟨84281781791872269235033267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112375709055829692313377689 84281781791872269235033267)
      ·
        refine ⟨126422672687808403852549901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84281781791872269235033267 126422672687808403852549901)
        ·
          refine ⟨47408502257928151444706213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126422672687808403852549901 47408502257928151444706213)
          ·
            refine ⟨8889094173361528395882415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47408502257928151444706213 8889094173361528395882415)
            ·
              refine ⟨13333641260042292593823623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8889094173361528395882415 13333641260042292593823623)
              ·
                refine ⟨20000461890063438890735435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13333641260042292593823623 20000461890063438890735435)
                ·
                  refine ⟨30000692835095158336103153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20000461890063438890735435 30000692835095158336103153)
                  ·
                    refine ⟨22500519626321368752077365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30000692835095158336103153 22500519626321368752077365)
                    ·
                      refine ⟨2109423714967628320507253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22500519626321368752077365 2109423714967628320507253)
                      ·
                        rfl

theorem cell23_4108088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_4108088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108088 prefixEnd_4108088 := by exact prefixLift 4108088
  have htrace : WordTrace (prefixWord ++ tailWord_4108088) baseStart_4108088 baseEnd_4108088 := by
    simpa [prefixWord, tailWord_4108088, baseEnd_4108088] using wordTrace_append hprefix tailTrace_4108088
  have hstable : (prefixWord ++ tailWord_4108088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108088).length < 2 ^ (prefixWord ++ tailWord_4108088).sum := by decide
  have hdescent : baseEnd_4108088 < baseStart_4108088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108135 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_4108135 : Nat := 118140960795 + 4108135 * 2 ^ 59
def prefixEnd_4108135 : Nat := 4983230072969 + 3 ^ 40 * 4108135 * 2
def baseEnd_4108135 : Nat := 2109447848558389636619537

theorem tailTrace_4108135 : CollatzResearch.WordTrace tailWord_4108135 prefixEnd_4108135 2109447848558389636619537 := by
  unfold tailWord_4108135
  simp only [CollatzResearch.WordTrace]
  refine ⟨149835992971935983444797859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99890661981290655629865239 149835992971935983444797859)
  ·
    refine ⟨224753989457903975167196789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149835992971935983444797859 224753989457903975167196789)
    ·
      refine ⟨21070686511678497671924699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224753989457903975167196789 21070686511678497671924699)
      ·
        refine ⟨31606029767517746507887049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21070686511678497671924699 31606029767517746507887049)
        ·
          refine ⟨23704522325638309880915287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31606029767517746507887049 23704522325638309880915287)
          ·
            refine ⟨35556783488457464821372931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23704522325638309880915287 35556783488457464821372931)
            ·
              refine ⟨53335175232686197232059397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35556783488457464821372931 53335175232686197232059397)
              ·
                refine ⟨10000345356128661981011137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53335175232686197232059397 10000345356128661981011137)
                ·
                  refine ⟨7500259017096496485758353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10000345356128661981011137 7500259017096496485758353)
                  ·
                    refine ⟨5625194262822372364318765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7500259017096496485758353 5625194262822372364318765)
                    ·
                      refine ⟨2109447848558389636619537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5625194262822372364318765 2109447848558389636619537)
                      ·
                        rfl

theorem cell23_4108135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_4108135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108135 prefixEnd_4108135 := by exact prefixLift 4108135
  have htrace : WordTrace (prefixWord ++ tailWord_4108135) baseStart_4108135 baseEnd_4108135 := by
    simpa [prefixWord, tailWord_4108135, baseEnd_4108135] using wordTrace_append hprefix tailTrace_4108135
  have hstable : (prefixWord ++ tailWord_4108135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108135).length < 2 ^ (prefixWord ++ tailWord_4108135).sum := by decide
  have hdescent : baseEnd_4108135 < baseStart_4108135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108199 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_4108199 : Nat := 118140960795 + 4108199 * 2 ^ 59
def prefixEnd_4108199 : Nat := 4983230072969 + 3 ^ 40 * 4108199 * 2
def baseEnd_4108199 : Nat := 2109480711320277386219243

theorem tailTrace_4108199 : CollatzResearch.WordTrace tailWord_4108199 prefixEnd_4108199 2109480711320277386219243 := by
  unfold tailWord_4108199
  simp only [CollatzResearch.WordTrace]
  refine ⟨149838327243704122375127651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99892218162469414916751767 149838327243704122375127651)
  ·
    refine ⟨224757490865556183562691477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149838327243704122375127651 224757490865556183562691477)
    ·
      refine ⟨10535507384322946104501163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224757490865556183562691477 10535507384322946104501163)
      ·
        refine ⟨15803261076484419156751745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10535507384322946104501163 15803261076484419156751745)
        ·
          refine ⟨11852445807363314367563809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15803261076484419156751745 11852445807363314367563809)
          ·
            refine ⟨8889334355522485775672857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11852445807363314367563809 8889334355522485775672857)
            ·
              refine ⟨6667000766641864331754643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8889334355522485775672857 6667000766641864331754643)
              ·
                refine ⟨10000501149962796497631965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667000766641864331754643 10000501149962796497631965)
                ·
                  refine ⟨3750187931236048686611987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10000501149962796497631965 3750187931236048686611987)
                  ·
                    refine ⟨5625281896854073029917981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3750187931236048686611987 5625281896854073029917981)
                    ·
                      refine ⟨2109480711320277386219243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5625281896854073029917981 2109480711320277386219243)
                      ·
                        rfl

theorem cell23_4108199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_4108199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108199 prefixEnd_4108199 := by exact prefixLift 4108199
  have htrace : WordTrace (prefixWord ++ tailWord_4108199) baseStart_4108199 baseEnd_4108199 := by
    simpa [prefixWord, tailWord_4108199, baseEnd_4108199] using wordTrace_append hprefix tailTrace_4108199
  have hstable : (prefixWord ++ tailWord_4108199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108199).length < 2 ^ (prefixWord ++ tailWord_4108199).sum := by decide
  have hdescent : baseEnd_4108199 < baseStart_4108199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108222 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_4108222 : Nat := 118140960795 + 4108222 * 2 ^ 59
def prefixEnd_4108222 : Nat := 4983230072969 + 3 ^ 40 * 4108222 * 2
def baseEnd_4108222 : Nat := 2109492521375330796231637

theorem tailTrace_4108222 : CollatzResearch.WordTrace tailWord_4108222 prefixEnd_4108222 2109492521375330796231637 := by
  unfold tailWord_4108222
  simp only [CollatzResearch.WordTrace]
  refine ⟨18729895765327599662901865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99892777415080531535476613 18729895765327599662901865)
  ·
    refine ⟨14047421823995699747176399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18729895765327599662901865 14047421823995699747176399)
    ·
      refine ⟨21071132735993549620764599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14047421823995699747176399 21071132735993549620764599)
      ·
        refine ⟨31606699103990324431146899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21071132735993549620764599 31606699103990324431146899)
        ·
          refine ⟨47410048655985486646720349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31606699103990324431146899 47410048655985486646720349)
          ·
            refine ⟨17778768245994557492520131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47410048655985486646720349 17778768245994557492520131)
            ·
              refine ⟨26668152368991836238780197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17778768245994557492520131 26668152368991836238780197)
              ·
                refine ⟨5000278569185969294771287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26668152368991836238780197 5000278569185969294771287)
                ·
                  refine ⟨7500417853778953942156931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000278569185969294771287 7500417853778953942156931)
                  ·
                    refine ⟨11250626780668430913235397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7500417853778953942156931 11250626780668430913235397)
                    ·
                      refine ⟨2109492521375330796231637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11250626780668430913235397 2109492521375330796231637)
                      ·
                        rfl

theorem cell23_4108222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_4108222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108222 prefixEnd_4108222 := by exact prefixLift 4108222
  have htrace : WordTrace (prefixWord ++ tailWord_4108222) baseStart_4108222 baseEnd_4108222 := by
    simpa [prefixWord, tailWord_4108222, baseEnd_4108222] using wordTrace_append hprefix tailTrace_4108222
  have hstable : (prefixWord ++ tailWord_4108222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108222).length < 2 ^ (prefixWord ++ tailWord_4108222).sum := by decide
  have hdescent : baseEnd_4108222 < baseStart_4108222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108245 : List Nat := [1, 3, 2, 3, 2, 3, 9]
def baseStart_4108245 : Nat := 118140960795 + 4108245 * 2 ^ 59
def prefixEnd_4108245 : Nat := 4983230072969 + 3 ^ 40 * 4108245 * 2
def baseEnd_4108245 : Nat := 26043263350992397607951

theorem tailTrace_4108245 : CollatzResearch.WordTrace tailWord_4108245 prefixEnd_4108245 26043263350992397607951 := by
  unfold tailWord_4108245
  simp only [CollatzResearch.WordTrace]
  refine ⟨149840005001537472231302189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99893336667691648154201459 149840005001537472231302189)
  ·
    refine ⟨56190001875576552086738321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149840005001537472231302189 56190001875576552086738321)
    ·
      refine ⟨42142501406682414065053741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56190001875576552086738321 42142501406682414065053741)
      ·
        refine ⟨15803438027505905274395153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42142501406682414065053741 15803438027505905274395153)
        ·
          refine ⟨11852578520629428955796365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15803438027505905274395153 11852578520629428955796365)
          ·
            refine ⟨4444716945236035858423637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11852578520629428955796365 4444716945236035858423637)
            ·
              refine ⟨26043263350992397607951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4444716945236035858423637 26043263350992397607951)
              ·
                rfl

theorem cell23_4108245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 9].length) (baseStart_4108245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108245 prefixEnd_4108245 := by exact prefixLift 4108245
  have htrace : WordTrace (prefixWord ++ tailWord_4108245) baseStart_4108245 baseEnd_4108245 := by
    simpa [prefixWord, tailWord_4108245, baseEnd_4108245] using wordTrace_append hprefix tailTrace_4108245
  have hstable : (prefixWord ++ tailWord_4108245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108245).length < 2 ^ (prefixWord ++ tailWord_4108245).sum := by decide
  have hdescent : baseEnd_4108245 < baseStart_4108245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108288 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 3, 8]
def baseStart_4108288 : Nat := 118140960795 + 4108288 * 2 ^ 59
def prefixEnd_4108288 : Nat := 4983230072969 + 3 ^ 40 * 4108288 * 2
def baseEnd_4108288 : Nat := 703175470366175846002111

theorem tailTrace_4108288 : CollatzResearch.WordTrace tailWord_4108288 prefixEnd_4108288 703175470366175846002111 := by
  unfold tailWord_4108288
  simp only [CollatzResearch.WordTrace]
  refine ⟨74920786670190845287558759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99894382226921127050078345 74920786670190845287558759)
  ·
    refine ⟨112381180005286267931338139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74920786670190845287558759 112381180005286267931338139)
    ·
      refine ⟨168571770007929401897007209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112381180005286267931338139 168571770007929401897007209)
      ·
        refine ⟨126428827505947051422755407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168571770007929401897007209 126428827505947051422755407)
        ·
          refine ⟨189643241258920577134133111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126428827505947051422755407 189643241258920577134133111)
          ·
            refine ⟨284464861888380865701199667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189643241258920577134133111 284464861888380865701199667)
            ·
              refine ⟨426697292832571298551799501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284464861888380865701199667 426697292832571298551799501)
              ·
                refine ⟨160011484812214236956924813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426697292832571298551799501 160011484812214236956924813)
                ·
                  refine ⟨60004306804580338858846805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160011484812214236956924813 60004306804580338858846805)
                  ·
                    refine ⟨703175470366175846002111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60004306804580338858846805 703175470366175846002111)
                    ·
                      rfl

theorem cell23_4108288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_4108288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108288 prefixEnd_4108288 := by exact prefixLift 4108288
  have htrace : WordTrace (prefixWord ++ tailWord_4108288) baseStart_4108288 baseEnd_4108288 := by
    simpa [prefixWord, tailWord_4108288, baseEnd_4108288] using wordTrace_append hprefix tailTrace_4108288
  have hstable : (prefixWord ++ tailWord_4108288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108288).length < 2 ^ (prefixWord ++ tailWord_4108288).sum := by decide
  have hdescent : baseEnd_4108288 < baseStart_4108288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108312 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 3, 4, 2]
def baseStart_4108312 : Nat := 118140960795 + 4108312 * 2 ^ 59
def prefixEnd_4108312 : Nat := 4983230072969 + 3 ^ 40 * 4108312 * 2
def baseEnd_4108312 : Nat := 2109538734634235444106223

theorem tailTrace_4108312 : CollatzResearch.WordTrace tailWord_4108312 prefixEnd_4108312 2109538734634235444106223 := by
  unfold tailWord_4108312
  simp only [CollatzResearch.WordTrace]
  refine ⟨74921224346147371336995595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99894965794863161782660793 74921224346147371336995595)
  ·
    refine ⟨112381836519221057005493393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74921224346147371336995595 112381836519221057005493393)
    ·
      refine ⟨84286377389415792754120045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112381836519221057005493393 84286377389415792754120045)
      ·
        refine ⟨31607391521030922282795017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84286377389415792754120045 31607391521030922282795017)
        ·
          refine ⟨23705543640773191712096263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31607391521030922282795017 23705543640773191712096263)
          ·
            refine ⟨35558315461159787568144395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23705543640773191712096263 35558315461159787568144395)
            ·
              refine ⟨53337473191739681352216593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35558315461159787568144395 53337473191739681352216593)
              ·
                refine ⟨40003104893804761014162445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53337473191739681352216593 40003104893804761014162445)
                ·
                  refine ⟨15001164335176785380310917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40003104893804761014162445 15001164335176785380310917)
                  ·
                    refine ⟨2812718312845647258808297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15001164335176785380310917 2812718312845647258808297)
                    ·
                      refine ⟨2109538734634235444106223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812718312845647258808297 2109538734634235444106223)
                      ·
                        rfl

theorem cell23_4108312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_4108312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108312 prefixEnd_4108312 := by exact prefixLift 4108312
  have htrace : WordTrace (prefixWord ++ tailWord_4108312) baseStart_4108312 baseEnd_4108312 := by
    simpa [prefixWord, tailWord_4108312, baseEnd_4108312] using wordTrace_append hprefix tailTrace_4108312
  have hstable : (prefixWord ++ tailWord_4108312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108312).length < 2 ^ (prefixWord ++ tailWord_4108312).sum := by decide
  have hdescent : baseEnd_4108312 < baseStart_4108312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108325 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_4108325 : Nat := 118140960795 + 4108325 * 2 ^ 59
def prefixEnd_4108325 : Nat := 4983230072969 + 3 ^ 40 * 4108325 * 2
def baseEnd_4108325 : Nat := 2109545409882743893243663

theorem tailTrace_4108325 : CollatzResearch.WordTrace tailWord_4108325 prefixEnd_4108325 2109545409882743893243663 := by
  unfold tailWord_4108325
  simp only [CollatzResearch.WordTrace]
  refine ⟨149842922841247645894214429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99895281894165097262809619 149842922841247645894214429)
  ·
    refine ⟨56191096065467867210330411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149842922841247645894214429 56191096065467867210330411)
    ·
      refine ⟨84286644098201800815495617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56191096065467867210330411 84286644098201800815495617)
      ·
        refine ⟨63214983073651350611621713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84286644098201800815495617 63214983073651350611621713)
        ·
          refine ⟨47411237305238512958716285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63214983073651350611621713 47411237305238512958716285)
          ·
            refine ⟨17779213989464442359518607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47411237305238512958716285 17779213989464442359518607)
            ·
              refine ⟨26668820984196663539277911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17779213989464442359518607 26668820984196663539277911)
              ·
                refine ⟨40003231476294995308916867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26668820984196663539277911 40003231476294995308916867)
                ·
                  refine ⟨60004847214442492963375301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40003231476294995308916867 60004847214442492963375301)
                  ·
                    refine ⟨11250908852707967430632869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60004847214442492963375301 11250908852707967430632869)
                    ·
                      refine ⟨2109545409882743893243663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11250908852707967430632869 2109545409882743893243663)
                      ·
                        rfl

theorem cell23_4108325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_4108325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108325 prefixEnd_4108325 := by exact prefixLift 4108325
  have htrace : WordTrace (prefixWord ++ tailWord_4108325) baseStart_4108325 baseEnd_4108325 := by
    simpa [prefixWord, tailWord_4108325, baseEnd_4108325] using wordTrace_append hprefix tailTrace_4108325
  have hstable : (prefixWord ++ tailWord_4108325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108325).length < 2 ^ (prefixWord ++ tailWord_4108325).sum := by decide
  have hdescent : baseEnd_4108325 < baseStart_4108325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108342 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4108342 : Nat := 118140960795 + 4108342 * 2 ^ 59
def prefixEnd_4108342 : Nat := 4983230072969 + 3 ^ 40 * 4108342 * 2
def baseEnd_4108342 : Nat := 2109554139053870326731085

theorem tailTrace_4108342 : CollatzResearch.WordTrace tailWord_4108342 prefixEnd_4108342 2109554139053870326731085 := by
  unfold tailWord_4108342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9365221430136628612348955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99895695254790705198388853 9365221430136628612348955)
  ·
    refine ⟨14047832145204942918523433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9365221430136628612348955 14047832145204942918523433)
    ·
      refine ⟨10535874108903707188892575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14047832145204942918523433 10535874108903707188892575)
      ·
        refine ⟨15803811163355560783338863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10535874108903707188892575 15803811163355560783338863)
        ·
          refine ⟨23705716745033341175008295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15803811163355560783338863 23705716745033341175008295)
          ·
            refine ⟨35558575117550011762512443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23705716745033341175008295 35558575117550011762512443)
            ·
              refine ⟨53337862676325017643768665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35558575117550011762512443 53337862676325017643768665)
              ·
                refine ⟨40003397007243763232826499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53337862676325017643768665 40003397007243763232826499)
                ·
                  refine ⟨60005095510865644849239749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40003397007243763232826499 60005095510865644849239749)
                  ·
                    refine ⟨11250955408287308409232453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60005095510865644849239749 11250955408287308409232453)
                    ·
                      refine ⟨2109554139053870326731085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11250955408287308409232453 2109554139053870326731085)
                      ·
                        rfl

theorem cell23_4108342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4108342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108342 prefixEnd_4108342 := by exact prefixLift 4108342
  have htrace : WordTrace (prefixWord ++ tailWord_4108342) baseStart_4108342 baseEnd_4108342 := by
    simpa [prefixWord, tailWord_4108342, baseEnd_4108342] using wordTrace_append hprefix tailTrace_4108342
  have hstable : (prefixWord ++ tailWord_4108342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108342).length < 2 ^ (prefixWord ++ tailWord_4108342).sum := by decide
  have hdescent : baseEnd_4108342 < baseStart_4108342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108350 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_4108350 : Nat := 118140960795 + 4108350 * 2 ^ 59
def prefixEnd_4108350 : Nat := 4983230072969 + 3 ^ 40 * 4108350 * 2
def baseEnd_4108350 : Nat := 2109558246899106295431049

theorem tailTrace_4108350 : CollatzResearch.WordTrace tailWord_4108350 prefixEnd_4108350 2109558246899106295431049 := by
  unfold tailWord_4108350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18730479333269634395484313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99895889777438050109249669 18730479333269634395484313)
  ·
    refine ⟨14047859499952225796613235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18730479333269634395484313 14047859499952225796613235)
    ·
      refine ⟨21071789249928338694919853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14047859499952225796613235 21071789249928338694919853)
      ·
        refine ⟨7901920968723127010594945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21071789249928338694919853 7901920968723127010594945)
        ·
          refine ⟨5926440726542345257946209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7901920968723127010594945 5926440726542345257946209)
          ·
            refine ⟨4444830544906758943459657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5926440726542345257946209 4444830544906758943459657)
            ·
              refine ⟨3333622908680069207594743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4444830544906758943459657 3333622908680069207594743)
              ·
                refine ⟨5000434363020103811392115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333622908680069207594743 5000434363020103811392115)
                ·
                  refine ⟨7500651544530155717088173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000434363020103811392115 7500651544530155717088173)
                  ·
                    refine ⟨2812744329198808393908065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7500651544530155717088173 2812744329198808393908065)
                    ·
                      refine ⟨2109558246899106295431049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812744329198808393908065 2109558246899106295431049)
                      ·
                        rfl

theorem cell23_4108350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_4108350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108350 prefixEnd_4108350 := by exact prefixLift 4108350
  have htrace : WordTrace (prefixWord ++ tailWord_4108350) baseStart_4108350 baseEnd_4108350 := by
    simpa [prefixWord, tailWord_4108350, baseEnd_4108350] using wordTrace_append hprefix tailTrace_4108350
  have hstable : (prefixWord ++ tailWord_4108350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108350).length < 2 ^ (prefixWord ++ tailWord_4108350).sum := by decide
  have hdescent : baseEnd_4108350 < baseStart_4108350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108352 : List Nat := [2, 1, 1, 2, 2, 4, 1, 5, 5]
def baseStart_4108352 : Nat := 118140960795 + 4108352 * 2 ^ 59
def prefixEnd_4108352 : Nat := 4983230072969 + 3 ^ 40 * 4108352 * 2
def baseEnd_4108352 : Nat := 234395474873379476400671

theorem tailTrace_4108352 : CollatzResearch.WordTrace tailWord_4108352 prefixEnd_4108352 234395474873379476400671 := by
  unfold tailWord_4108352
  simp only [CollatzResearch.WordTrace]
  refine ⟨74921953806074914752723655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99895938408099886336964873 74921953806074914752723655)
  ·
    refine ⟨112382930709112372129085483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74921953806074914752723655 112382930709112372129085483)
    ·
      refine ⟨168574396063668558193628225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112382930709112372129085483 168574396063668558193628225)
      ·
        refine ⟨126430797047751418645221169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168574396063668558193628225 126430797047751418645221169)
        ·
          refine ⟨94823097785813563983915877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126430797047751418645221169 94823097785813563983915877)
          ·
            refine ⟨17779330834840043246984227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94823097785813563983915877 17779330834840043246984227)
            ·
              refine ⟨26668996252260064870476341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17779330834840043246984227 26668996252260064870476341)
              ·
                refine ⟨2500218398649381081607157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26668996252260064870476341 2500218398649381081607157)
                ·
                  refine ⟨234395474873379476400671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2500218398649381081607157 234395474873379476400671)
                  ·
                    rfl

theorem cell23_4108352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 5].length) (baseStart_4108352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108352 prefixEnd_4108352 := by exact prefixLift 4108352
  have htrace : WordTrace (prefixWord ++ tailWord_4108352) baseStart_4108352 baseEnd_4108352 := by
    simpa [prefixWord, tailWord_4108352, baseEnd_4108352] using wordTrace_append hprefix tailTrace_4108352
  have hstable : (prefixWord ++ tailWord_4108352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108352).length < 2 ^ (prefixWord ++ tailWord_4108352).sum := by decide
  have hdescent : baseEnd_4108352 < baseStart_4108352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108375 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_4108375 : Nat := 118140960795 + 4108375 * 2 ^ 59
def prefixEnd_4108375 : Nat := 4983230072969 + 3 ^ 40 * 4108375 * 2
def baseEnd_4108375 : Nat := 2109571083915468697618433

theorem tailTrace_4108375 : CollatzResearch.WordTrace tailWord_4108375 prefixEnd_4108375 2109571083915468697618433 := by
  unfold tailWord_4108375
  simp only [CollatzResearch.WordTrace]
  refine ⟨149844746491066504433534579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99896497660711002955689719 149844746491066504433534579)
  ·
    refine ⟨224767119736599756650301869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149844746491066504433534579 224767119736599756650301869)
    ·
      refine ⟨84287669901224908743863201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224767119736599756650301869 84287669901224908743863201)
      ·
        refine ⟨63215752425918681557897401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84287669901224908743863201 63215752425918681557897401)
        ·
          refine ⟨47411814319439011168423051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63215752425918681557897401 47411814319439011168423051)
          ·
            refine ⟨71117721479158516752634577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47411814319439011168423051 71117721479158516752634577)
            ·
              refine ⟨53338291109368887564475933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71117721479158516752634577 53338291109368887564475933)
              ·
                refine ⟨20001859166013332836678475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53338291109368887564475933 20001859166013332836678475)
                ·
                  refine ⟨30002788749019999255017713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20001859166013332836678475 30002788749019999255017713)
                  ·
                    refine ⟨22502091561764999441263285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30002788749019999255017713 22502091561764999441263285)
                    ·
                      refine ⟨2109571083915468697618433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22502091561764999441263285 2109571083915468697618433)
                      ·
                        rfl

theorem cell23_4108375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_4108375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108375 prefixEnd_4108375 := by exact prefixLift 4108375
  have htrace : WordTrace (prefixWord ++ tailWord_4108375) baseStart_4108375 baseEnd_4108375 := by
    simpa [prefixWord, tailWord_4108375, baseEnd_4108375] using wordTrace_append hprefix tailTrace_4108375
  have hstable : (prefixWord ++ tailWord_4108375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108375).length < 2 ^ (prefixWord ++ tailWord_4108375).sum := by decide
  have hdescent : baseEnd_4108375 < baseStart_4108375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108402 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_4108402 : Nat := 118140960795 + 4108402 * 2 ^ 59
def prefixEnd_4108402 : Nat := 4983230072969 + 3 ^ 40 * 4108402 * 2
def baseEnd_4108402 : Nat := 2109584947893140091980809

theorem tailTrace_4108402 : CollatzResearch.WordTrace tailWord_4108402 prefixEnd_4108402 2109584947893140091980809 := by
  unfold tailWord_4108402
  simp only [CollatzResearch.WordTrace]
  refine ⟨37461432815492172011191865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99897154174645792029844973 37461432815492172011191865)
  ·
    refine ⟨28096074611619129008393899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37461432815492172011191865 28096074611619129008393899)
    ·
      refine ⟨42144111917428693512590849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28096074611619129008393899 42144111917428693512590849)
      ·
        refine ⟨31608083938071520134443137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42144111917428693512590849 31608083938071520134443137)
        ·
          refine ⟨23706062953553640100832353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31608083938071520134443137 23706062953553640100832353)
          ·
            refine ⟨17779547215165230075624265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23706062953553640100832353 17779547215165230075624265)
            ·
              refine ⟨13334660411373922556718199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17779547215165230075624265 13334660411373922556718199)
              ·
                refine ⟨20001990617060883835077299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13334660411373922556718199 20001990617060883835077299)
                ·
                  refine ⟨30002985925591325752615949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20001990617060883835077299 30002985925591325752615949)
                  ·
                    refine ⟨11251119722096747157230981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30002985925591325752615949 11251119722096747157230981)
                    ·
                      refine ⟨2109584947893140091980809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11251119722096747157230981 2109584947893140091980809)
                      ·
                        rfl

theorem cell23_4108402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_4108402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108402 prefixEnd_4108402 := by exact prefixLift 4108402
  have htrace : WordTrace (prefixWord ++ tailWord_4108402) baseStart_4108402 baseEnd_4108402 := by
    simpa [prefixWord, tailWord_4108402, baseEnd_4108402] using wordTrace_append hprefix tailTrace_4108402
  have hstable : (prefixWord ++ tailWord_4108402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108402).length < 2 ^ (prefixWord ++ tailWord_4108402).sum := by decide
  have hdescent : baseEnd_4108402 < baseStart_4108402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108425 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 8]
def baseStart_4108425 : Nat := 118140960795 + 4108425 * 2 ^ 59
def prefixEnd_4108425 : Nat := 4983230072969 + 3 ^ 40 * 4108425 * 2
def baseEnd_4108425 : Nat := 234399639772021500221467

theorem tailTrace_4108425 : CollatzResearch.WordTrace tailWord_4108425 prefixEnd_4108425 234399639772021500221467 := by
  unfold tailWord_4108425
  simp only [CollatzResearch.WordTrace]
  refine ⟨149846570140885362972854729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99897713427256908648569819 149846570140885362972854729)
  ·
    refine ⟨112384927605664022229641047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149846570140885362972854729 112384927605664022229641047)
    ·
      refine ⟨168577391408496033344461571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112384927605664022229641047 168577391408496033344461571)
      ·
        refine ⟨252866087112744050016692357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168577391408496033344461571 252866087112744050016692357)
        ·
          refine ⟨47412391333639509378129817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252866087112744050016692357 47412391333639509378129817)
          ·
            refine ⟨35559293500229632033597363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47412391333639509378129817 35559293500229632033597363)
            ·
              refine ⟨53338940250344448050396045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35559293500229632033597363 53338940250344448050396045)
              ·
                refine ⟨20002102593879168018898517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53338940250344448050396045 20002102593879168018898517)
                ·
                  refine ⟨234399639772021500221467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20002102593879168018898517 234399639772021500221467)
                  ·
                    rfl

theorem cell23_4108425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 8].length) (baseStart_4108425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108425 prefixEnd_4108425 := by exact prefixLift 4108425
  have htrace : WordTrace (prefixWord ++ tailWord_4108425) baseStart_4108425 baseEnd_4108425 := by
    simpa [prefixWord, tailWord_4108425, baseEnd_4108425] using wordTrace_append hprefix tailTrace_4108425
  have hstable : (prefixWord ++ tailWord_4108425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108425).length < 2 ^ (prefixWord ++ tailWord_4108425).sum := by decide
  have hdescent : baseEnd_4108425 < baseStart_4108425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108519 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 1, 6]
def baseStart_4108519 : Nat := 118140960795 + 4108519 * 2 ^ 59
def prefixEnd_4108519 : Nat := 4983230072969 + 3 ^ 40 * 4108519 * 2
def baseEnd_4108519 : Nat := 703215008376572044739257

theorem tailTrace_4108519 : CollatzResearch.WordTrace tailWord_4108519 prefixEnd_4108519 703215008376572044739257 := by
  unfold tailWord_4108519
  simp only [CollatzResearch.WordTrace]
  refine ⟨149849998602544817026776611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99899999068363211351184407 149849998602544817026776611)
  ·
    refine ⟨224774997903817225540164917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149849998602544817026776611 224774997903817225540164917)
    ·
      refine ⟨21072656053482864894390461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224774997903817225540164917 21072656053482864894390461)
      ·
        refine ⟨7902246020056074335396423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21072656053482864894390461 7902246020056074335396423)
        ·
          refine ⟨11853369030084111503094635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902246020056074335396423 11853369030084111503094635)
          ·
            refine ⟨17780053545126167254641953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11853369030084111503094635 17780053545126167254641953)
            ·
              refine ⟨13335040158844625440981465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17780053545126167254641953 13335040158844625440981465)
              ·
                refine ⟨10001280119133469080736099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13335040158844625440981465 10001280119133469080736099)
                ·
                  refine ⟨15001920178700203621104149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10001280119133469080736099 15001920178700203621104149)
                  ·
                    refine ⟨703215008376572044739257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15001920178700203621104149 703215008376572044739257)
                    ·
                      rfl

theorem cell23_4108519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_4108519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108519 prefixEnd_4108519 := by exact prefixLift 4108519
  have htrace : WordTrace (prefixWord ++ tailWord_4108519) baseStart_4108519 baseEnd_4108519 := by
    simpa [prefixWord, tailWord_4108519, baseEnd_4108519] using wordTrace_append hprefix tailTrace_4108519
  have hstable : (prefixWord ++ tailWord_4108519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108519).length < 2 ^ (prefixWord ++ tailWord_4108519).sum := by decide
  have hdescent : baseEnd_4108519 < baseStart_4108519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108526 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_4108526 : Nat := 118140960795 + 4108526 * 2 ^ 59
def prefixEnd_4108526 : Nat := 4983230072969 + 3 ^ 40 * 4108526 * 2
def baseEnd_4108526 : Nat := 2109648619494297606830239

theorem tailTrace_4108526 : CollatzResearch.WordTrace tailWord_4108526 prefixEnd_4108526 2109648619494297606830239 := by
  unfold tailWord_4108526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18731281739189932152785179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99900169275679638148187621 18731281739189932152785179)
  ·
    refine ⟨28096922608784898229177769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18731281739189932152785179 28096922608784898229177769)
    ·
      refine ⟨21072691956588673671883327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28096922608784898229177769 21072691956588673671883327)
      ·
        refine ⟨31609037934883010507824991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21072691956588673671883327 31609037934883010507824991)
        ·
          refine ⟨47413556902324515761737487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31609037934883010507824991 47413556902324515761737487)
          ·
            refine ⟨71120335353486773642606231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47413556902324515761737487 71120335353486773642606231)
            ·
              refine ⟨106680503030230160463909347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71120335353486773642606231 106680503030230160463909347)
              ·
                refine ⟨160020754545345240695864021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106680503030230160463909347 160020754545345240695864021)
                ·
                  refine ⟨3750486434656529078809313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160020754545345240695864021 3750486434656529078809313)
                  ·
                    refine ⟨2812864825992396809106985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3750486434656529078809313 2812864825992396809106985)
                    ·
                      refine ⟨2109648619494297606830239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812864825992396809106985 2109648619494297606830239)
                      ·
                        rfl

theorem cell23_4108526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_4108526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108526 prefixEnd_4108526 := by exact prefixLift 4108526
  have htrace : WordTrace (prefixWord ++ tailWord_4108526) baseStart_4108526 baseEnd_4108526 := by
    simpa [prefixWord, tailWord_4108526, baseEnd_4108526] using wordTrace_append hprefix tailTrace_4108526
  have hstable : (prefixWord ++ tailWord_4108526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108526).length < 2 ^ (prefixWord ++ tailWord_4108526).sum := by decide
  have hdescent : baseEnd_4108526 < baseStart_4108526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108543 : List Nat := [1, 1, 2, 2, 1, 4, 1, 6, 1, 2, 2]
def baseStart_4108543 : Nat := 118140960795 + 4108543 * 2 ^ 59
def prefixEnd_4108543 : Nat := 4983230072969 + 3 ^ 40 * 4108543 * 2
def baseEnd_4108543 : Nat := 2109657348665424040317661

theorem tailTrace_4108543 : CollatzResearch.WordTrace tailWord_4108543 prefixEnd_4108543 2109657348665424040317661 := by
  unfold tailWord_4108543
  simp only [CollatzResearch.WordTrace]
  refine ⟨149850873954457869125650283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99900582636305246083766855 149850873954457869125650283)
  ·
    refine ⟨224776310931686803688475425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149850873954457869125650283 224776310931686803688475425)
    ·
      refine ⟨168582233198765102766356569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224776310931686803688475425 168582233198765102766356569)
      ·
        refine ⟨126436674899073827074767427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168582233198765102766356569 126436674899073827074767427)
        ·
          refine ⟨189655012348610740612151141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126436674899073827074767427 189655012348610740612151141)
          ·
            refine ⟨35560314815364513864778339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189655012348610740612151141 35560314815364513864778339)
            ·
              refine ⟨53340472223046770797167509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35560314815364513864778339 53340472223046770797167509)
              ·
                refine ⟨2500334635455317381117227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53340472223046770797167509 2500334635455317381117227)
                ·
                  refine ⟨3750501953182976071675841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500334635455317381117227 3750501953182976071675841)
                  ·
                    refine ⟨2812876464887232053756881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3750501953182976071675841 2812876464887232053756881)
                    ·
                      refine ⟨2109657348665424040317661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812876464887232053756881 2109657348665424040317661)
                      ·
                        rfl

theorem cell23_4108543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 2, 2].length) (baseStart_4108543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108543 prefixEnd_4108543 := by exact prefixLift 4108543
  have htrace : WordTrace (prefixWord ++ tailWord_4108543) baseStart_4108543 baseEnd_4108543 := by
    simpa [prefixWord, tailWord_4108543, baseEnd_4108543] using wordTrace_append hprefix tailTrace_4108543
  have hstable : (prefixWord ++ tailWord_4108543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108543).length < 2 ^ (prefixWord ++ tailWord_4108543).sum := by decide
  have hdescent : baseEnd_4108543 < baseStart_4108543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108546 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4108546 : Nat := 118140960795 + 4108546 * 2 ^ 59
def prefixEnd_4108546 : Nat := 4983230072969 + 3 ^ 40 * 4108546 * 2
def baseEnd_4108546 : Nat := 2109658889107387528580147

theorem tailTrace_4108546 : CollatzResearch.WordTrace tailWord_4108546 prefixEnd_4108546 2109658889107387528580147 := by
  unfold tailWord_4108546
  simp only [CollatzResearch.WordTrace]
  refine ⟨37462745843361750159502373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99900655582298000425339661 37462745843361750159502373)
  ·
    refine ⟨7024264845630328154906695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37462745843361750159502373 7024264845630328154906695)
    ·
      refine ⟨10536397268445492232360043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024264845630328154906695 10536397268445492232360043)
      ·
        refine ⟨15804595902668238348540065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10536397268445492232360043 15804595902668238348540065)
        ·
          refine ⟨11853446927001178761405049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15804595902668238348540065 11853446927001178761405049)
          ·
            refine ⟨8890085195250884071053787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11853446927001178761405049 8890085195250884071053787)
            ·
              refine ⟨13335127792876326106580681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8890085195250884071053787 13335127792876326106580681)
              ·
                refine ⟨10001345844657244579935511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13335127792876326106580681 10001345844657244579935511)
                ·
                  refine ⟨15002018766985866869903267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10001345844657244579935511 15002018766985866869903267)
                  ·
                    refine ⟨22503028150478800304854901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15002018766985866869903267 22503028150478800304854901)
                    ·
                      refine ⟨2109658889107387528580147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22503028150478800304854901 2109658889107387528580147)
                      ·
                        rfl

theorem cell23_4108546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4108546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108546 prefixEnd_4108546 := by exact prefixLift 4108546
  have htrace : WordTrace (prefixWord ++ tailWord_4108546) baseStart_4108546 baseEnd_4108546 := by
    simpa [prefixWord, tailWord_4108546, baseEnd_4108546] using wordTrace_append hprefix tailTrace_4108546
  have hstable : (prefixWord ++ tailWord_4108546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108546).length < 2 ^ (prefixWord ++ tailWord_4108546).sum := by decide
  have hdescent : baseEnd_4108546 < baseStart_4108546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108576 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 4, 1, 3]
def baseStart_4108576 : Nat := 118140960795 + 4108576 * 2 ^ 59
def prefixEnd_4108576 : Nat := 4983230072969 + 3 ^ 40 * 4108576 * 2
def baseEnd_4108576 : Nat := 2109674293527022411205009

theorem tailTrace_4108576 : CollatzResearch.WordTrace tailWord_4108576 prefixEnd_4108576 2109674293527022411205009 := by
  unfold tailWord_4108576
  simp only [CollatzResearch.WordTrace]
  refine ⟨74926038781669157880800791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99901385042225543841067721 74926038781669157880800791)
  ·
    refine ⟨112389058172503736821201187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74926038781669157880800791 112389058172503736821201187)
    ·
      refine ⟨168583587258755605231801781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112389058172503736821201187 168583587258755605231801781)
      ·
        refine ⟨15804711305508337990481417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168583587258755605231801781 15804711305508337990481417)
        ·
          refine ⟨11853533479131253492861063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15804711305508337990481417 11853533479131253492861063)
          ·
            refine ⟨17780300218696880239291595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11853533479131253492861063 17780300218696880239291595)
            ·
              refine ⟨26670450328045320358937393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17780300218696880239291595 26670450328045320358937393)
              ·
                refine ⟨20002837746033990269203045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26670450328045320358937393 20002837746033990269203045)
                ·
                  refine ⟨3750532077381373175475571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20002837746033990269203045 3750532077381373175475571)
                  ·
                    refine ⟨5625798116072059763213357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3750532077381373175475571 5625798116072059763213357)
                    ·
                      refine ⟨2109674293527022411205009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5625798116072059763213357 2109674293527022411205009)
                      ·
                        rfl

theorem cell23_4108576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_4108576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108576 prefixEnd_4108576 := by exact prefixLift 4108576
  have htrace : WordTrace (prefixWord ++ tailWord_4108576) baseStart_4108576 baseEnd_4108576 := by
    simpa [prefixWord, tailWord_4108576, baseEnd_4108576] using wordTrace_append hprefix tailTrace_4108576
  have hstable : (prefixWord ++ tailWord_4108576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108576).length < 2 ^ (prefixWord ++ tailWord_4108576).sum := by decide
  have hdescent : baseEnd_4108576 < baseStart_4108576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108583 : List Nat := [1, 1, 8, 1, 1, 2, 9]
def baseStart_4108583 : Nat := 118140960795 + 4108583 * 2 ^ 59
def prefixEnd_4108583 : Nat := 4983230072969 + 3 ^ 40 * 4108583 * 2
def baseEnd_4108583 : Nat := 26045406023353134368117

theorem tailTrace_4108583 : CollatzResearch.WordTrace tailWord_4108583 prefixEnd_4108583 26045406023353134368117 := by
  unfold tailWord_4108583
  simp only [CollatzResearch.WordTrace]
  refine ⟨149852332874312955957106403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99901555249541970638070935 149852332874312955957106403)
  ·
    refine ⟨224778499311469433935659605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149852332874312955957106403 224778499311469433935659605)
    ·
      refine ⟨2634123038806282428933511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 224778499311469433935659605 2634123038806282428933511)
      ·
        refine ⟨3951184558209423643400267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2634123038806282428933511 3951184558209423643400267)
        ·
          refine ⟨5926776837314135465100401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3951184558209423643400267 5926776837314135465100401)
          ·
            refine ⟨4445082627985601598825301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5926776837314135465100401 4445082627985601598825301)
            ·
              refine ⟨26045406023353134368117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4445082627985601598825301 26045406023353134368117)
              ·
                rfl

theorem cell23_4108583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 9].length) (baseStart_4108583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108583 prefixEnd_4108583 := by exact prefixLift 4108583
  have htrace : WordTrace (prefixWord ++ tailWord_4108583) baseStart_4108583 baseEnd_4108583 := by
    simpa [prefixWord, tailWord_4108583, baseEnd_4108583] using wordTrace_append hprefix tailTrace_4108583
  have hstable : (prefixWord ++ tailWord_4108583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108583).length < 2 ^ (prefixWord ++ tailWord_4108583).sum := by decide
  have hdescent : baseEnd_4108583 < baseStart_4108583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108592 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 2, 6]
def baseStart_4108592 : Nat := 118140960795 + 4108592 * 2 ^ 59
def prefixEnd_4108592 : Nat := 4983230072969 + 3 ^ 40 * 4108592 * 2
def baseEnd_4108592 : Nat := 703227503072498116201645

theorem tailTrace_4108592 : CollatzResearch.WordTrace tailWord_4108592 prefixEnd_4108592 703227503072498116201645 := by
  unfold tailWord_4108592
  simp only [CollatzResearch.WordTrace]
  refine ⟨74926330565640175247092015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99901774087520233662789353 74926330565640175247092015)
  ·
    refine ⟨112389495848460262870638023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74926330565640175247092015 112389495848460262870638023)
    ·
      refine ⟨168584243772690394305957035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112389495848460262870638023 168584243772690394305957035)
      ·
        refine ⟨252876365659035591458935553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168584243772690394305957035 252876365659035591458935553)
        ·
          refine ⟨189657274244276693594201665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252876365659035591458935553 189657274244276693594201665)
          ·
            refine ⟨142242955683207520195651249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189657274244276693594201665 142242955683207520195651249)
            ·
              refine ⟨106682216762405640146738437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142242955683207520195651249 106682216762405640146738437)
              ·
                refine ⟨20002915642951057527513457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106682216762405640146738437 20002915642951057527513457)
                ·
                  refine ⟨15002186732213293145635093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20002915642951057527513457 15002186732213293145635093)
                  ·
                    refine ⟨703227503072498116201645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15002186732213293145635093 703227503072498116201645)
                    ·
                      rfl

theorem cell23_4108592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_4108592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108592 prefixEnd_4108592 := by exact prefixLift 4108592
  have htrace : WordTrace (prefixWord ++ tailWord_4108592) baseStart_4108592 baseEnd_4108592 := by
    simpa [prefixWord, tailWord_4108592, baseEnd_4108592] using wordTrace_append hprefix tailTrace_4108592
  have hstable : (prefixWord ++ tailWord_4108592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108592).length < 2 ^ (prefixWord ++ tailWord_4108592).sum := by decide
  have hdescent : baseEnd_4108592 < baseStart_4108592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108632 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_4108632 : Nat := 118140960795 + 4108632 * 2 ^ 59
def prefixEnd_4108632 : Nat := 4983230072969 + 3 ^ 40 * 4108632 * 2
def baseEnd_4108632 : Nat := 2109703048443674192104751

theorem tailTrace_4108632 : CollatzResearch.WordTrace tailWord_4108632 prefixEnd_4108632 2109703048443674192104751 := by
  unfold tailWord_4108632
  simp only [CollatzResearch.WordTrace]
  refine ⟨74927060025567718662820075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99902746700756958217093433 74927060025567718662820075)
  ·
    refine ⟨112390590038351577994230113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74927060025567718662820075 112390590038351577994230113)
    ·
      refine ⟨84292942528763683495672585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112390590038351577994230113 84292942528763683495672585)
      ·
        refine ⟨63219706896572762621754439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84292942528763683495672585 63219706896572762621754439)
        ·
          refine ⟨94829560344859143932631659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63219706896572762621754439 94829560344859143932631659)
          ·
            refine ⟨142244340517288715898947489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94829560344859143932631659 142244340517288715898947489)
            ·
              refine ⟨106683255387966536924210617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142244340517288715898947489 106683255387966536924210617)
              ·
                refine ⟨80012441540974902693157963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106683255387966536924210617 80012441540974902693157963)
                ·
                  refine ⟨120018662311462354039736945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80012441540974902693157963 120018662311462354039736945)
                  ·
                    refine ⟨90013996733596765529802709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120018662311462354039736945 90013996733596765529802709)
                    ·
                      refine ⟨2109703048443674192104751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90013996733596765529802709 2109703048443674192104751)
                      ·
                        rfl

theorem cell23_4108632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_4108632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108632 prefixEnd_4108632 := by exact prefixLift 4108632
  have htrace : WordTrace (prefixWord ++ tailWord_4108632) baseStart_4108632 baseEnd_4108632 := by
    simpa [prefixWord, tailWord_4108632, baseEnd_4108632] using wordTrace_append hprefix tailTrace_4108632
  have hstable : (prefixWord ++ tailWord_4108632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108632).length < 2 ^ (prefixWord ++ tailWord_4108632).sum := by decide
  have hdescent : baseEnd_4108632 < baseStart_4108632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108649 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 3]
def baseStart_4108649 : Nat := 118140960795 + 4108649 * 2 ^ 59
def prefixEnd_4108649 : Nat := 4983230072969 + 3 ^ 40 * 4108649 * 2
def baseEnd_4108649 : Nat := 2109711777614800625592173

theorem tailTrace_4108649 : CollatzResearch.WordTrace tailWord_4108649 prefixEnd_4108649 2109711777614800625592173 := by
  unfold tailWord_4108649
  simp only [CollatzResearch.WordTrace]
  refine ⟨149854740092073849229009001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99903160061382566152672667 149854740092073849229009001)
  ·
    refine ⟨112391055069055386921756751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149854740092073849229009001 112391055069055386921756751)
    ·
      refine ⟨168586582603583080382635127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112391055069055386921756751 168586582603583080382635127)
      ·
        refine ⟨252879873905374620573952691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168586582603583080382635127 252879873905374620573952691)
        ·
          refine ⟨379319810858061930860929037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252879873905374620573952691 379319810858061930860929037)
          ·
            refine ⟨142244929071773224072848389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379319810858061930860929037 142244929071773224072848389)
            ·
              refine ⟨26670924200957479513659073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142244929071773224072848389 26670924200957479513659073)
              ·
                refine ⟨20003193150718109635244305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26670924200957479513659073 20003193150718109635244305)
                ·
                  refine ⟨15002394863038582226433229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20003193150718109635244305 15002394863038582226433229)
                  ·
                    refine ⟨5625898073639468334912461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15002394863038582226433229 5625898073639468334912461)
                    ·
                      refine ⟨2109711777614800625592173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5625898073639468334912461 2109711777614800625592173)
                      ·
                        rfl

theorem cell23_4108649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_4108649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108649 prefixEnd_4108649 := by exact prefixLift 4108649
  have htrace : WordTrace (prefixWord ++ tailWord_4108649) baseStart_4108649 baseEnd_4108649 := by
    simpa [prefixWord, tailWord_4108649, baseEnd_4108649] using wordTrace_append hprefix tailTrace_4108649
  have hstable : (prefixWord ++ tailWord_4108649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108649).length < 2 ^ (prefixWord ++ tailWord_4108649).sum := by decide
  have hdescent : baseEnd_4108649 < baseStart_4108649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108650 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_4108650 : Nat := 118140960795 + 4108650 * 2 ^ 59
def prefixEnd_4108650 : Nat := 4983230072969 + 3 ^ 40 * 4108650 * 2
def baseEnd_4108650 : Nat := 2109712291095455121679669

theorem tailTrace_4108650 : CollatzResearch.WordTrace tailWord_4108650 prefixEnd_4108650 2109712291095455121679669 := by
  unfold tailWord_4108650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37463694141267556599948851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99903184376713484266530269 37463694141267556599948851)
  ·
    refine ⟨56195541211901334899923277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37463694141267556599948851 56195541211901334899923277)
    ·
      refine ⟨21073327954463000587471229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56195541211901334899923277 21073327954463000587471229)
      ·
        refine ⟨7902497982923625220301711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21073327954463000587471229 7902497982923625220301711)
        ·
          refine ⟨11853746974385437830452567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902497982923625220301711 11853746974385437830452567)
          ·
            refine ⟨17780620461578156745678851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11853746974385437830452567 17780620461578156745678851)
            ·
              refine ⟨26670930692367235118518277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17780620461578156745678851 26670930692367235118518277)
              ·
                refine ⟨5000799504818856584722177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26670930692367235118518277 5000799504818856584722177)
                ·
                  refine ⟨3750599628614142438541633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5000799504818856584722177 3750599628614142438541633)
                  ·
                    refine ⟨2812949721460606828906225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3750599628614142438541633 2812949721460606828906225)
                    ·
                      refine ⟨2109712291095455121679669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812949721460606828906225 2109712291095455121679669)
                      ·
                        rfl

theorem cell23_4108650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_4108650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108650 prefixEnd_4108650 := by exact prefixLift 4108650
  have htrace : WordTrace (prefixWord ++ tailWord_4108650) baseStart_4108650 baseEnd_4108650 := by
    simpa [prefixWord, tailWord_4108650, baseEnd_4108650] using wordTrace_append hprefix tailTrace_4108650
  have hstable : (prefixWord ++ tailWord_4108650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108650).length < 2 ^ (prefixWord ++ tailWord_4108650).sum := by decide
  have hdescent : baseEnd_4108650 < baseStart_4108650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108656 : List Nat := [2, 1, 1, 1, 4, 4, 1, 4, 5]
def baseStart_4108656 : Nat := 118140960795 + 4108656 * 2 ^ 59
def prefixEnd_4108656 : Nat := 4983230072969 + 3 ^ 40 * 4108656 * 2
def baseEnd_4108656 : Nat := 234412819108820233133849

theorem tailTrace_4108656 : CollatzResearch.WordTrace tailWord_4108656 prefixEnd_4108656 234412819108820233133849 := by
  unfold tailWord_4108656
  simp only [CollatzResearch.WordTrace]
  refine ⟨74927497701524244712256911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99903330268698992949675881 74927497701524244712256911)
  ·
    refine ⟨112391246552286367068385367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74927497701524244712256911 112391246552286367068385367)
    ·
      refine ⟨168586869828429550602578051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112391246552286367068385367 168586869828429550602578051)
      ·
        refine ⟨252880304742644325903867077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168586869828429550602578051 252880304742644325903867077)
        ·
          refine ⟨47415057139245811106975077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252880304742644325903867077 47415057139245811106975077)
          ·
            refine ⟨8890323213608589582557827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47415057139245811106975077 8890323213608589582557827)
            ·
              refine ⟨13335484820412884373836741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8890323213608589582557827 13335484820412884373836741)
              ·
                refine ⟨2500403403827415820094389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13335484820412884373836741 2500403403827415820094389)
                ·
                  refine ⟨234412819108820233133849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2500403403827415820094389 234412819108820233133849)
                  ·
                    rfl

theorem cell23_4108656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 5].length) (baseStart_4108656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108656 prefixEnd_4108656 := by exact prefixLift 4108656
  have htrace : WordTrace (prefixWord ++ tailWord_4108656) baseStart_4108656 baseEnd_4108656 := by
    simpa [prefixWord, tailWord_4108656, baseEnd_4108656] using wordTrace_append hprefix tailTrace_4108656
  have hstable : (prefixWord ++ tailWord_4108656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108656).length < 2 ^ (prefixWord ++ tailWord_4108656).sum := by decide
  have hdescent : baseEnd_4108656 < baseStart_4108656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108676 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_4108676 : Nat := 118140960795 + 4108676 * 2 ^ 59
def prefixEnd_4108676 : Nat := 4983230072969 + 3 ^ 40 * 4108676 * 2
def baseEnd_4108676 : Nat := 2109725641592472019954549

theorem tailTrace_4108676 : CollatzResearch.WordTrace tailWord_4108676 prefixEnd_4108676 2109725641592472019954549 := by
  unfold tailWord_4108676
  simp only [CollatzResearch.WordTrace]
  refine ⟨74927862431488016420120941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99903816575317355226827921 74927862431488016420120941)
  ·
    refine ⟨28097948411808006157545353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74927862431488016420120941 28097948411808006157545353)
    ·
      refine ⟨21073461308856004618159015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28097948411808006157545353 21073461308856004618159015)
      ·
        refine ⟨31610191963284006927238523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21073461308856004618159015 31610191963284006927238523)
        ·
          refine ⟨47415287944926010390857785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31610191963284006927238523 47415287944926010390857785)
          ·
            refine ⟨35561465958694507793143339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47415287944926010390857785 35561465958694507793143339)
            ·
              refine ⟨53342198938041761689715009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35561465958694507793143339 53342198938041761689715009)
              ·
                refine ⟨40006649203531321267286257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53342198938041761689715009 40006649203531321267286257)
                ·
                  refine ⟨30004986902648490950464693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40006649203531321267286257 30004986902648490950464693)
                  ·
                    refine ⟨2812967522123296026606065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30004986902648490950464693 2812967522123296026606065)
                    ·
                      refine ⟨2109725641592472019954549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2812967522123296026606065 2109725641592472019954549)
                      ·
                        rfl

theorem cell23_4108676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_4108676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108676 prefixEnd_4108676 := by exact prefixLift 4108676
  have htrace : WordTrace (prefixWord ++ tailWord_4108676) baseStart_4108676 baseEnd_4108676 := by
    simpa [prefixWord, tailWord_4108676, baseEnd_4108676] using wordTrace_append hprefix tailTrace_4108676
  have hstable : (prefixWord ++ tailWord_4108676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108676).length < 2 ^ (prefixWord ++ tailWord_4108676).sum := by decide
  have hdescent : baseEnd_4108676 < baseStart_4108676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108686 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_4108686 : Nat := 118140960795 + 4108686 * 2 ^ 59
def prefixEnd_4108686 : Nat := 4983230072969 + 3 ^ 40 * 4108686 * 2
def baseEnd_4108686 : Nat := 703243592133005660276501

theorem tailTrace_4108686 : CollatzResearch.WordTrace tailWord_4108686 prefixEnd_4108686 703243592133005660276501 := by
  unfold tailWord_4108686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732011199117475568513239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99904059728626536365403941 18732011199117475568513239)
  ·
    refine ⟨28098016798676213352769859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18732011199117475568513239 28098016798676213352769859)
    ·
      refine ⟨42147025198014320029154789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28098016798676213352769859 42147025198014320029154789)
      ·
        refine ⟨7902567224627685005466523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42147025198014320029154789 7902567224627685005466523)
        ·
          refine ⟨11853850836941527508199785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902567224627685005466523 11853850836941527508199785)
          ·
            refine ⟨8890388127706145631149839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11853850836941527508199785 8890388127706145631149839)
            ·
              refine ⟨13335582191559218446724759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8890388127706145631149839 13335582191559218446724759)
              ·
                refine ⟨20003373287338827670087139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13335582191559218446724759 20003373287338827670087139)
                ·
                  refine ⟨30005059931008241505130709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20003373287338827670087139 30005059931008241505130709)
                  ·
                    refine ⟨703243592133005660276501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30005059931008241505130709 703243592133005660276501)
                    ·
                      rfl

theorem cell23_4108686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_4108686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108686 prefixEnd_4108686 := by exact prefixLift 4108686
  have htrace : WordTrace (prefixWord ++ tailWord_4108686) baseStart_4108686 baseEnd_4108686 := by
    simpa [prefixWord, tailWord_4108686, baseEnd_4108686] using wordTrace_append hprefix tailTrace_4108686
  have hstable : (prefixWord ++ tailWord_4108686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108686).length < 2 ^ (prefixWord ++ tailWord_4108686).sum := by decide
  have hdescent : baseEnd_4108686 < baseStart_4108686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108706 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_4108706 : Nat := 118140960795 + 4108706 * 2 ^ 59
def prefixEnd_4108706 : Nat := 4983230072969 + 3 ^ 40 * 4108706 * 2
def baseEnd_4108706 : Nat := 2109741046012106902579411

theorem tailTrace_4108706 : CollatzResearch.WordTrace tailWord_4108706 prefixEnd_4108706 2109741046012106902579411 := by
  unfold tailWord_4108706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37464204763216836990958493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99904546035244898642555981 37464204763216836990958493)
  ·
    refine ⟨14049076786206313871609435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37464204763216836990958493 14049076786206313871609435)
    ·
      refine ⟨21073615179309470807414153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14049076786206313871609435 21073615179309470807414153)
      ·
        refine ⟨15805211384482103105560615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21073615179309470807414153 15805211384482103105560615)
        ·
          refine ⟨23707817076723154658340923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15805211384482103105560615 23707817076723154658340923)
          ·
            refine ⟨35561725615084731987511385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23707817076723154658340923 35561725615084731987511385)
            ·
              refine ⟨26671294211313548990633539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35561725615084731987511385 26671294211313548990633539)
              ·
                refine ⟨40006941316970323485950309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26671294211313548990633539 40006941316970323485950309)
                ·
                  refine ⟨7501301496931935653615683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40006941316970323485950309 7501301496931935653615683)
                  ·
                    refine ⟨11251952245397903480423525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7501301496931935653615683 11251952245397903480423525)
                    ·
                      refine ⟨2109741046012106902579411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11251952245397903480423525 2109741046012106902579411)
                      ·
                        rfl

theorem cell23_4108706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_4108706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108706 prefixEnd_4108706 := by exact prefixLift 4108706
  have htrace : WordTrace (prefixWord ++ tailWord_4108706) baseStart_4108706 baseEnd_4108706 := by
    simpa [prefixWord, tailWord_4108706, baseEnd_4108706] using wordTrace_append hprefix tailTrace_4108706
  have hstable : (prefixWord ++ tailWord_4108706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108706).length < 2 ^ (prefixWord ++ tailWord_4108706).sum := by decide
  have hdescent : baseEnd_4108706 < baseStart_4108706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108739 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 3]
def baseStart_4108739 : Nat := 118140960795 + 4108739 * 2 ^ 59
def prefixEnd_4108739 : Nat := 4983230072969 + 3 ^ 40 * 4108739 * 2
def baseEnd_4108739 : Nat := 2109757990873705273466759

theorem tailTrace_4108739 : CollatzResearch.WordTrace tailWord_4108739 prefixEnd_4108739 2109757990873705273466759 := by
  unfold tailWord_4108739
  simp only [CollatzResearch.WordTrace]
  refine ⟨149858022661747794599785271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99905348441165196399856847 149858022661747794599785271)
  ·
    refine ⟨224787033992621691899677907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149858022661747794599785271 224787033992621691899677907)
    ·
      refine ⟨337180550988932537849516861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224787033992621691899677907 337180550988932537849516861)
      ·
        refine ⟨126442706620849701693568823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337180550988932537849516861 126442706620849701693568823)
        ·
          refine ⟨189664059931274552540353235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126442706620849701693568823 189664059931274552540353235)
          ·
            refine ⟨284496089896911828810529853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189664059931274552540353235 284496089896911828810529853)
            ·
              refine ⟨106686033711341935803948695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284496089896911828810529853 106686033711341935803948695)
              ·
                refine ⟨160029050567012903705923043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106686033711341935803948695 160029050567012903705923043)
                ·
                  refine ⟨240043575850519355558884565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160029050567012903705923043 240043575850519355558884565)
                  ·
                    refine ⟨5626021308996547395911357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 240043575850519355558884565 5626021308996547395911357)
                    ·
                      refine ⟨2109757990873705273466759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5626021308996547395911357 2109757990873705273466759)
                      ·
                        rfl

theorem cell23_4108739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_4108739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108739 prefixEnd_4108739 := by exact prefixLift 4108739
  have htrace : WordTrace (prefixWord ++ tailWord_4108739) baseStart_4108739 baseEnd_4108739 := by
    simpa [prefixWord, tailWord_4108739, baseEnd_4108739] using wordTrace_append hprefix tailTrace_4108739
  have hstable : (prefixWord ++ tailWord_4108739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108739).length < 2 ^ (prefixWord ++ tailWord_4108739).sum := by decide
  have hdescent : baseEnd_4108739 < baseStart_4108739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108759 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 7, 5]
def baseStart_4108759 : Nat := 118140960795 + 4108759 * 2 ^ 59
def prefixEnd_4108759 : Nat := 4983230072969 + 3 ^ 40 * 4108759 * 2
def baseEnd_4108759 : Nat := 703256086828931731738889

theorem tailTrace_4108759 : CollatzResearch.WordTrace tailWord_4108759 prefixEnd_4108759 703256086828931731738889 := by
  unfold tailWord_4108759
  simp only [CollatzResearch.WordTrace]
  refine ⟨149858752121675338015513331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99905834747783558677008887 149858752121675338015513331)
  ·
    refine ⟨224788128182513007023269997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149858752121675338015513331 224788128182513007023269997)
    ·
      refine ⟨84295548068442377633726249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224788128182513007023269997 84295548068442377633726249)
      ·
        refine ⟨63221661051331783225294687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84295548068442377633726249 63221661051331783225294687)
        ·
          refine ⟨94832491576997674837942031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63221661051331783225294687 94832491576997674837942031)
          ·
            refine ⟨142248737365496512256913047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94832491576997674837942031 142248737365496512256913047)
            ·
              refine ⟨213373106048244768385369571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142248737365496512256913047 213373106048244768385369571)
              ·
                refine ⟨320059659072367152578054357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213373106048244768385369571 320059659072367152578054357)
                ·
                  refine ⟨7501398259508605138548149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 320059659072367152578054357 7501398259508605138548149)
                  ·
                    refine ⟨703256086828931731738889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7501398259508605138548149 703256086828931731738889)
                    ·
                      rfl

theorem cell23_4108759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_4108759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108759 prefixEnd_4108759 := by exact prefixLift 4108759
  have htrace : WordTrace (prefixWord ++ tailWord_4108759) baseStart_4108759 baseEnd_4108759 := by
    simpa [prefixWord, tailWord_4108759, baseEnd_4108759] using wordTrace_append hprefix tailTrace_4108759
  have hstable : (prefixWord ++ tailWord_4108759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108759).length < 2 ^ (prefixWord ++ tailWord_4108759).sum := by decide
  have hdescent : baseEnd_4108759 < baseStart_4108759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108809 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_4108809 : Nat := 118140960795 + 4108809 * 2 ^ 59
def prefixEnd_4108809 : Nat := 4983230072969 + 3 ^ 40 * 4108809 * 2
def baseEnd_4108809 : Nat := 2109793934519519999591437

theorem tailTrace_4108809 : CollatzResearch.WordTrace tailWord_4108809 prefixEnd_4108809 2109793934519519999591437 := by
  unfold tailWord_4108809
  simp only [CollatzResearch.WordTrace]
  refine ⟨149860575771494196554833481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99907050514329464369888987 149860575771494196554833481)
  ·
    refine ⟨112395431828620647416125111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149860575771494196554833481 112395431828620647416125111)
    ·
      refine ⟨168593147742930971124187667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112395431828620647416125111 168593147742930971124187667)
      ·
        refine ⟨252889721614396456686281501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168593147742930971124187667 252889721614396456686281501)
        ·
          refine ⟨94833645605398671257355563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252889721614396456686281501 94833645605398671257355563)
          ·
            refine ⟨142250468408098006886033345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94833645605398671257355563 142250468408098006886033345)
            ·
              refine ⟨106687851306073505164525009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142250468408098006886033345 106687851306073505164525009)
              ·
                refine ⟨80015888479555128873393757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106687851306073505164525009 80015888479555128873393757)
                ·
                  refine ⟨30005958179833173327522659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80015888479555128873393757 30005958179833173327522659)
                  ·
                    refine ⟨45008937269749759991283989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30005958179833173327522659 45008937269749759991283989)
                    ·
                      refine ⟨2109793934519519999591437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45008937269749759991283989 2109793934519519999591437)
                      ·
                        rfl

theorem cell23_4108809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_4108809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108809 prefixEnd_4108809 := by exact prefixLift 4108809
  have htrace : WordTrace (prefixWord ++ tailWord_4108809) baseStart_4108809 baseEnd_4108809 := by
    simpa [prefixWord, tailWord_4108809, baseEnd_4108809] using wordTrace_append hprefix tailTrace_4108809
  have hstable : (prefixWord ++ tailWord_4108809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108809).length < 2 ^ (prefixWord ++ tailWord_4108809).sum := by decide
  have hdescent : baseEnd_4108809 < baseStart_4108809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
