import V185TrunkScan21Chunk115

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1411004 : List Nat := [2, 2, 2, 5, 1, 1, 1, 7]
def baseStart_1411004 : Nat := 118140960795 + 1411004 * 2 ^ 59
def prefixEnd_1411004 : Nat := 4983230072969 + 3 ^ 40 * 1411004 * 2
def baseEnd_1411004 : Nat := 107336778876548544305321

theorem tailTrace_1411004 : CollatzResearch.WordTrace tailWord_1411004 prefixEnd_1411004 107336778876548544305321 := by
  unfold tailWord_1411004
  simp only [CollatzResearch.WordTrace]
  refine ⟨25731771890090481571444033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34309029186787308761925377 25731771890090481571444033)
  ·
    refine ⟨19298828917567861178583025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25731771890090481571444033 19298828917567861178583025)
    ·
      refine ⟨14474121688175895883937269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19298828917567861178583025 14474121688175895883937269)
      ·
        refine ⟨1356948908266490239119119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14474121688175895883937269 1356948908266490239119119)
        ·
          refine ⟨2035423362399735358678679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356948908266490239119119 2035423362399735358678679)
          ·
            refine ⟨3053135043599603038018019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035423362399735358678679 3053135043599603038018019)
            ·
              refine ⟨4579702565399404557027029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053135043599603038018019 4579702565399404557027029)
              ·
                refine ⟨107336778876548544305321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4579702565399404557027029 107336778876548544305321)
                ·
                  rfl

theorem cell21_1411004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_1411004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411004 prefixEnd_1411004 := by exact prefixLift 1411004
  have htrace : WordTrace (prefixWord ++ tailWord_1411004) baseStart_1411004 baseEnd_1411004 := by
    simpa [prefixWord, tailWord_1411004, baseEnd_1411004] using wordTrace_append hprefix tailTrace_1411004
  have hstable : (prefixWord ++ tailWord_1411004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411004).length < 2 ^ (prefixWord ++ tailWord_1411004).sum := by decide
  have hdescent : baseEnd_1411004 < baseStart_1411004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411032 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_1411032 : Nat := 118140960795 + 1411032 * 2 ^ 59
def prefixEnd_1411032 : Nat := 4983230072969 + 3 ^ 40 * 1411032 * 2
def baseEnd_1411032 : Nat := 322016726611123806449239

theorem tailTrace_1411032 : CollatzResearch.WordTrace tailWord_1411032 prefixEnd_1411032 322016726611123806449239 := by
  unfold tailWord_1411032
  simp only [CollatzResearch.WordTrace]
  refine ⟨25732282512039761962453675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34309710016053015949938233 25732282512039761962453675)
  ·
    refine ⟨38598423768059642943680513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25732282512039761962453675 38598423768059642943680513)
    ·
      refine ⟨28948817826044732207760385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38598423768059642943680513 28948817826044732207760385)
      ·
        refine ⟨21711613369533549155820289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28948817826044732207760385 21711613369533549155820289)
        ·
          refine ⟨16283710027150161866865217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21711613369533549155820289 16283710027150161866865217)
          ·
            refine ⟨12212782520362621400148913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16283710027150161866865217 12212782520362621400148913)
            ·
              refine ⟨9159586890271966050111685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12212782520362621400148913 9159586890271966050111685)
              ·
                refine ⟨1717422541925993634395941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9159586890271966050111685 1717422541925993634395941)
                ·
                  refine ⟨322016726611123806449239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717422541925993634395941 322016726611123806449239)
                  ·
                    rfl

theorem cell21_1411032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_1411032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411032 prefixEnd_1411032 := by exact prefixLift 1411032
  have htrace : WordTrace (prefixWord ++ tailWord_1411032) baseStart_1411032 baseEnd_1411032 := by
    simpa [prefixWord, tailWord_1411032, baseEnd_1411032] using wordTrace_append hprefix tailTrace_1411032
  have hstable : (prefixWord ++ tailWord_1411032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411032).length < 2 ^ (prefixWord ++ tailWord_1411032).sum := by decide
  have hdescent : baseEnd_1411032 < baseStart_1411032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411091 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 6]
def baseStart_1411091 : Nat := 118140960795 + 1411091 * 2 ^ 59
def prefixEnd_1411091 : Nat := 4983230072969 + 3 ^ 40 * 1411091 * 2
def baseEnd_1411091 : Nat := 322030191214952814965785

theorem tailTrace_1411091 : CollatzResearch.WordTrace tailWord_1411091 prefixEnd_1411091 322030191214952814965785 := by
  unfold tailWord_1411091
  simp only [CollatzResearch.WordTrace]
  refine ⟨51466716930865777001305127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34311144620577184667536751 51466716930865777001305127)
  ·
    refine ⟨77200075396298665501957691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51466716930865777001305127 77200075396298665501957691)
    ·
      refine ⟨115800113094447998252936537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77200075396298665501957691 115800113094447998252936537)
      ·
        refine ⟨86850084820835998689702403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115800113094447998252936537 86850084820835998689702403)
        ·
          refine ⟨130275127231253998034553605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86850084820835998689702403 130275127231253998034553605)
          ·
            refine ⟨24426586355860124631478801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130275127231253998034553605 24426586355860124631478801)
            ·
              refine ⟨18319939766895093473609101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24426586355860124631478801 18319939766895093473609101)
              ·
                refine ⟨6869977412585660052603413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18319939766895093473609101 6869977412585660052603413)
                ·
                  refine ⟨322030191214952814965785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6869977412585660052603413 322030191214952814965785)
                  ·
                    rfl

theorem cell21_1411091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_1411091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411091 prefixEnd_1411091 := by exact prefixLift 1411091
  have htrace : WordTrace (prefixWord ++ tailWord_1411091) baseStart_1411091 baseEnd_1411091 := by
    simpa [prefixWord, tailWord_1411091, baseEnd_1411091] using wordTrace_append hprefix tailTrace_1411091
  have hstable : (prefixWord ++ tailWord_1411091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411091).length < 2 ^ (prefixWord ++ tailWord_1411091).sum := by decide
  have hdescent : baseEnd_1411091 < baseStart_1411091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411111 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 5]
def baseStart_1411111 : Nat := 118140960795 + 1411111 * 2 ^ 59
def prefixEnd_1411111 : Nat := 4983230072969 + 3 ^ 40 * 1411111 * 2
def baseEnd_1411111 : Nat := 322034755487437224632411

theorem tailTrace_1411111 : CollatzResearch.WordTrace tailWord_1411111 prefixEnd_1411111 322034755487437224632411 := by
  unfold tailWord_1411111
  simp only [CollatzResearch.WordTrace]
  refine ⟨51467446390793320417033187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34311630927195546944688791 51467446390793320417033187)
  ·
    refine ⟨77201169586189980625549781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51467446390793320417033187 77201169586189980625549781)
    ·
      refine ⟨1809402412176327670911323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 77201169586189980625549781 1809402412176327670911323)
      ·
        refine ⟨2714103618264491506366985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809402412176327670911323 2714103618264491506366985)
        ·
          refine ⟨2035577713698368629775239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2714103618264491506366985 2035577713698368629775239)
          ·
            refine ⟨3053366570547552944662859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035577713698368629775239 3053366570547552944662859)
            ·
              refine ⟨4580049855821329416994289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053366570547552944662859 4580049855821329416994289)
              ·
                refine ⟨3435037391865997062745717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4580049855821329416994289 3435037391865997062745717)
                ·
                  refine ⟨322034755487437224632411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3435037391865997062745717 322034755487437224632411)
                  ·
                    rfl

theorem cell21_1411111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 5].length) (baseStart_1411111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411111 prefixEnd_1411111 := by exact prefixLift 1411111
  have htrace : WordTrace (prefixWord ++ tailWord_1411111) baseStart_1411111 baseEnd_1411111 := by
    simpa [prefixWord, tailWord_1411111, baseEnd_1411111] using wordTrace_append hprefix tailTrace_1411111
  have hstable : (prefixWord ++ tailWord_1411111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411111).length < 2 ^ (prefixWord ++ tailWord_1411111).sum := by decide
  have hdescent : baseEnd_1411111 < baseStart_1411111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411252 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1411252 : Nat := 118140960795 + 1411252 * 2 ^ 59
def prefixEnd_1411252 : Nat := 4983230072969 + 3 ^ 40 * 1411252 * 2
def baseEnd_1411252 : Nat := 322066933608452312782123

theorem tailTrace_1411252 : CollatzResearch.WordTrace tailWord_1411252 prefixEnd_1411252 322066933608452312782123 := by
  unfold tailWord_1411252
  simp only [CollatzResearch.WordTrace]
  refine ⟨25736294541641250748958005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34315059388855000998610673 25736294541641250748958005)
  ·
    refine ⟨2412777613278867257714813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25736294541641250748958005 2412777613278867257714813)
    ·
      refine ⟨904791604979575221643055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2412777613278867257714813 904791604979575221643055)
      ·
        refine ⟨1357187407469362832464583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904791604979575221643055 1357187407469362832464583)
        ·
          refine ⟨2035781111204044248696875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357187407469362832464583 2035781111204044248696875)
          ·
            refine ⟨3053671666806066373045313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035781111204044248696875 3053671666806066373045313)
            ·
              refine ⟨2290253750104549779783985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3053671666806066373045313 2290253750104549779783985)
              ·
                refine ⟨1717690312578412334837989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290253750104549779783985 1717690312578412334837989)
                ·
                  refine ⟨322066933608452312782123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717690312578412334837989 322066933608452312782123)
                  ·
                    rfl

theorem cell21_1411252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1411252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411252 prefixEnd_1411252 := by exact prefixLift 1411252
  have htrace : WordTrace (prefixWord ++ tailWord_1411252) baseStart_1411252 baseEnd_1411252 := by
    simpa [prefixWord, tailWord_1411252, baseEnd_1411252] using wordTrace_append hprefix tailTrace_1411252
  have hstable : (prefixWord ++ tailWord_1411252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411252).length < 2 ^ (prefixWord ++ tailWord_1411252).sum := by decide
  have hdescent : baseEnd_1411252 < baseStart_1411252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411322 : List Nat := [3, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_1411322 : Nat := 118140960795 + 1411322 * 2 ^ 59
def prefixEnd_1411322 : Nat := 4983230072969 + 3 ^ 40 * 1411322 * 2
def baseEnd_1411322 : Nat := 322082908562147746615313

theorem tailTrace_1411322 : CollatzResearch.WordTrace tailWord_1411322 prefixEnd_1411322 322082908562147746615313 := by
  unfold tailWord_1411322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12868785548257225863241055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34316761462019268968642813 12868785548257225863241055)
  ·
    refine ⟨19303178322385838794861583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12868785548257225863241055 19303178322385838794861583)
    ·
      refine ⟨28954767483578758192292375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19303178322385838794861583 28954767483578758192292375)
      ·
        refine ⟨43432151225368137288438563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28954767483578758192292375 43432151225368137288438563)
        ·
          refine ⟨65148226838052205932657845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43432151225368137288438563 65148226838052205932657845)
          ·
            refine ⟨6107646266067394306186673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65148226838052205932657845 6107646266067394306186673)
            ·
              refine ⟨4580734699550545729640005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6107646266067394306186673 4580734699550545729640005)
              ·
                refine ⟨858887756165727324307501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4580734699550545729640005 858887756165727324307501)
                ·
                  refine ⟨322082908562147746615313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858887756165727324307501 322082908562147746615313)
                  ·
                    rfl

theorem cell21_1411322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_1411322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411322 prefixEnd_1411322 := by exact prefixLift 1411322
  have htrace : WordTrace (prefixWord ++ tailWord_1411322) baseStart_1411322 baseEnd_1411322 := by
    simpa [prefixWord, tailWord_1411322, baseEnd_1411322] using wordTrace_append hprefix tailTrace_1411322
  have hstable : (prefixWord ++ tailWord_1411322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411322).length < 2 ^ (prefixWord ++ tailWord_1411322).sum := by decide
  have hdescent : baseEnd_1411322 < baseStart_1411322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411373 : List Nat := [1, 5, 3, 1, 2, 1, 3, 2, 3]
def baseStart_1411373 : Nat := 118140960795 + 1411373 * 2 ^ 59
def prefixEnd_1411373 : Nat := 4983230072969 + 3 ^ 40 * 1411373 * 2
def baseEnd_1411373 : Nat := 322094547456982991265209

theorem tailTrace_1411373 : CollatzResearch.WordTrace tailWord_1411373 prefixEnd_1411373 322094547456982991265209 := by
  unfold tailWord_1411373
  simp only [CollatzResearch.WordTrace]
  refine ⟨51477002315844139163070773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34318001543896092775380515 51477002315844139163070773)
  ·
    refine ⟨4825968967110388046537885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51477002315844139163070773 4825968967110388046537885)
    ·
      refine ⟨1809738362666395517451707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4825968967110388046537885 1809738362666395517451707)
      ·
        refine ⟨2714607543999593276177561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809738362666395517451707 2714607543999593276177561)
        ·
          refine ⟨2035955657999694957133171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2714607543999593276177561 2035955657999694957133171)
          ·
            refine ⟨3053933486999542435699757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035955657999694957133171 3053933486999542435699757)
            ·
              refine ⟨1145225057624828413387409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053933486999542435699757 1145225057624828413387409)
              ·
                refine ⟨858918793218621310040557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145225057624828413387409 858918793218621310040557)
                ·
                  refine ⟨322094547456982991265209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858918793218621310040557 322094547456982991265209)
                  ·
                    rfl

theorem cell21_1411373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_1411373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411373 prefixEnd_1411373 := by exact prefixLift 1411373
  have htrace : WordTrace (prefixWord ++ tailWord_1411373) baseStart_1411373 baseEnd_1411373 := by
    simpa [prefixWord, tailWord_1411373, baseEnd_1411373] using wordTrace_append hprefix tailTrace_1411373
  have hstable : (prefixWord ++ tailWord_1411373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411373).length < 2 ^ (prefixWord ++ tailWord_1411373).sum := by decide
  have hdescent : baseEnd_1411373 < baseStart_1411373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411426 : List Nat := [3, 3, 2, 1, 1, 11]
def baseStart_1411426 : Nat := 118140960795 + 1411426 * 2 ^ 59
def prefixEnd_1411426 : Nat := 4983230072969 + 3 ^ 40 * 1411426 * 2
def baseEnd_1411426 : Nat := 11929875658483950995621

theorem tailTrace_1411426 : CollatzResearch.WordTrace tailWord_1411426 prefixEnd_1411426 11929875658483950995621 := by
  unfold tailWord_1411426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12869733846163032303687533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34319290256434752809833421 12869733846163032303687533)
  ·
    refine ⟨4826150192311137113882825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12869733846163032303687533 4826150192311137113882825)
    ·
      refine ⟨3619612644233352835412119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4826150192311137113882825 3619612644233352835412119)
      ·
        refine ⟨5429418966350029253118179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619612644233352835412119 5429418966350029253118179)
        ·
          refine ⟨8144128449525043879677269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5429418966350029253118179 8144128449525043879677269)
          ·
            refine ⟨11929875658483950995621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8144128449525043879677269 11929875658483950995621)
            ·
              rfl

theorem cell21_1411426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 11].length) (baseStart_1411426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411426 prefixEnd_1411426 := by exact prefixLift 1411426
  have htrace : WordTrace (prefixWord ++ tailWord_1411426) baseStart_1411426 baseEnd_1411426 := by
    simpa [prefixWord, tailWord_1411426, baseEnd_1411426] using wordTrace_append hprefix tailTrace_1411426
  have hstable : (prefixWord ++ tailWord_1411426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411426).length < 2 ^ (prefixWord ++ tailWord_1411426).sum := by decide
  have hdescent : baseEnd_1411426 < baseStart_1411426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411432 : List Nat := [2, 1, 4, 2, 2, 3, 2, 2, 3]
def baseStart_1411432 : Nat := 118140960795 + 1411432 * 2 ^ 59
def prefixEnd_1411432 : Nat := 4983230072969 + 3 ^ 40 * 1411432 * 2
def baseEnd_1411432 : Nat := 322108012060811999781755

theorem tailTrace_1411432 : CollatzResearch.WordTrace tailWord_1411432 prefixEnd_1411432 322108012060811999781755 := by
  unfold tailWord_1411432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25739577111315196119734275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34319436148420261492979033 25739577111315196119734275)
  ·
    refine ⟨38609365666972794179601413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25739577111315196119734275 38609365666972794179601413)
    ·
      refine ⟨7239256062557398908675265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38609365666972794179601413 7239256062557398908675265)
      ·
        refine ⟨5429442046918049181506449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7239256062557398908675265 5429442046918049181506449)
        ·
          refine ⟨4072081535188536886129837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5429442046918049181506449 4072081535188536886129837)
          ·
            refine ⟨1527030575695701332298689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4072081535188536886129837 1527030575695701332298689)
            ·
              refine ⟨1145272931771775999224017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1527030575695701332298689 1145272931771775999224017)
              ·
                refine ⟨858954698828831999418013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145272931771775999224017 858954698828831999418013)
                ·
                  refine ⟨322108012060811999781755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858954698828831999418013 322108012060811999781755)
                  ·
                    rfl

theorem cell21_1411432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_1411432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411432 prefixEnd_1411432 := by exact prefixLift 1411432
  have htrace : WordTrace (prefixWord ++ tailWord_1411432) baseStart_1411432 baseEnd_1411432 := by
    simpa [prefixWord, tailWord_1411432, baseEnd_1411432] using wordTrace_append hprefix tailTrace_1411432
  have hstable : (prefixWord ++ tailWord_1411432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411432).length < 2 ^ (prefixWord ++ tailWord_1411432).sum := by decide
  have hdescent : baseEnd_1411432 < baseStart_1411432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411457 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 7]
def baseStart_1411457 : Nat := 118140960795 + 1411457 * 2 ^ 59
def prefixEnd_1411457 : Nat := 4983230072969 + 3 ^ 40 * 1411457 * 2
def baseEnd_1411457 : Nat := 322113717401417511865037

theorem tailTrace_1411457 : CollatzResearch.WordTrace tailWord_1411457 prefixEnd_1411457 322113717401417511865037 := by
  unfold tailWord_1411457
  simp only [CollatzResearch.WordTrace]
  refine ⟨51480066047539821509128625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34320044031693214339419083 51480066047539821509128625)
  ·
    refine ⟨38610049535654866131846469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51480066047539821509128625 38610049535654866131846469)
    ·
      refine ⟨7239384287935287399721213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38610049535654866131846469 7239384287935287399721213)
      ·
        refine ⟨2714769107975732774895455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7239384287935287399721213 2714769107975732774895455)
        ·
          refine ⟨4072153661963599162343183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2714769107975732774895455 4072153661963599162343183)
          ·
            refine ⟨6108230492945398743514775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072153661963599162343183 6108230492945398743514775)
            ·
              refine ⟨9162345739418098115272163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6108230492945398743514775 9162345739418098115272163)
              ·
                refine ⟨13743518609127147172908245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9162345739418098115272163 13743518609127147172908245)
                ·
                  refine ⟨322113717401417511865037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13743518609127147172908245 322113717401417511865037)
                  ·
                    rfl

theorem cell21_1411457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_1411457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411457 prefixEnd_1411457 := by exact prefixLift 1411457
  have htrace : WordTrace (prefixWord ++ tailWord_1411457) baseStart_1411457 baseEnd_1411457 := by
    simpa [prefixWord, tailWord_1411457, baseEnd_1411457] using wordTrace_append hprefix tailTrace_1411457
  have hstable : (prefixWord ++ tailWord_1411457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411457).length < 2 ^ (prefixWord ++ tailWord_1411457).sum := by decide
  have hdescent : baseEnd_1411457 < baseStart_1411457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411488 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_1411488 : Nat := 118140960795 + 1411488 * 2 ^ 59
def prefixEnd_1411488 : Nat := 4983230072969 + 3 ^ 40 * 1411488 * 2
def baseEnd_1411488 : Nat := 322120792023768346848307

theorem tailTrace_1411488 : CollatzResearch.WordTrace tailWord_1411488 prefixEnd_1411488 322120792023768346848307 := by
  unfold tailWord_1411488
  simp only [CollatzResearch.WordTrace]
  refine ⟨25740598355213756901753559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34320797806951675869004745 25740598355213756901753559)
  ·
    refine ⟨38610897532820635352630339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25740598355213756901753559 38610897532820635352630339)
    ·
      refine ⟨57916346299230953028945509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38610897532820635352630339 57916346299230953028945509)
      ·
        refine ⟨10859314931105803692927283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57916346299230953028945509 10859314931105803692927283)
        ·
          refine ⟨16288972396658705539390925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10859314931105803692927283 16288972396658705539390925)
          ·
            refine ⟨6108364648747014577271597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16288972396658705539390925 6108364648747014577271597)
            ·
              refine ⟨2290636743280130466476849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6108364648747014577271597 2290636743280130466476849)
              ·
                refine ⟨1717977557460097849857637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290636743280130466476849 1717977557460097849857637)
                ·
                  refine ⟨322120792023768346848307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717977557460097849857637 322120792023768346848307)
                  ·
                    rfl

theorem cell21_1411488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_1411488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411488 prefixEnd_1411488 := by exact prefixLift 1411488
  have htrace : WordTrace (prefixWord ++ tailWord_1411488) baseStart_1411488 baseEnd_1411488 := by
    simpa [prefixWord, tailWord_1411488, baseEnd_1411488] using wordTrace_append hprefix tailTrace_1411488
  have hstable : (prefixWord ++ tailWord_1411488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411488).length < 2 ^ (prefixWord ++ tailWord_1411488).sum := by decide
  have hdescent : baseEnd_1411488 < baseStart_1411488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411505 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 4]
def baseStart_1411505 : Nat := 118140960795 + 1411505 * 2 ^ 59
def prefixEnd_1411505 : Nat := 4983230072969 + 3 ^ 40 * 1411505 * 2
def baseEnd_1411505 : Nat := 322124671655380095064939

theorem tailTrace_1411505 : CollatzResearch.WordTrace tailWord_1411505 prefixEnd_1411505 322124671655380095064939 := by
  unfold tailWord_1411505
  simp only [CollatzResearch.WordTrace]
  refine ⟨51481816751365925706875969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34321211167577283804583979 51481816751365925706875969)
  ·
    refine ⟨38611362563524444280156977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51481816751365925706875969 38611362563524444280156977)
    ·
      refine ⟨28958521922643333210117733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38611362563524444280156977 28958521922643333210117733)
      ·
        refine ⟨5429722860495624976897075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28958521922643333210117733 5429722860495624976897075)
        ·
          refine ⟨8144584290743437465345613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5429722860495624976897075 8144584290743437465345613)
          ·
            refine ⟨3054219109028789049504605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8144584290743437465345613 3054219109028789049504605)
            ·
              refine ⟨1145332165885795893564227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3054219109028789049504605 1145332165885795893564227)
              ·
                refine ⟨1717998248828693840346341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145332165885795893564227 1717998248828693840346341)
                ·
                  refine ⟨322124671655380095064939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717998248828693840346341 322124671655380095064939)
                  ·
                    rfl

theorem cell21_1411505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_1411505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411505 prefixEnd_1411505 := by exact prefixLift 1411505
  have htrace : WordTrace (prefixWord ++ tailWord_1411505) baseStart_1411505 baseEnd_1411505 := by
    simpa [prefixWord, tailWord_1411505, baseEnd_1411505] using wordTrace_append hprefix tailTrace_1411505
  have hstable : (prefixWord ++ tailWord_1411505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411505).length < 2 ^ (prefixWord ++ tailWord_1411505).sum := by decide
  have hdescent : baseEnd_1411505 < baseStart_1411505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411609 : List Nat := [1, 2, 1, 2, 1, 1, 2, 8, 3]
def baseStart_1411609 : Nat := 118140960795 + 1411609 * 2 ^ 59
def prefixEnd_1411609 : Nat := 4983230072969 + 3 ^ 40 * 1411609 * 2
def baseEnd_1411609 : Nat := 322148405872299025331393

theorem tailTrace_1411609 : CollatzResearch.WordTrace tailWord_1411609 prefixEnd_1411609 322148405872299025331393 := by
  unfold tailWord_1411609
  simp only [CollatzResearch.WordTrace]
  refine ⟨51485609942989151468661881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34323739961992767645774587 51485609942989151468661881)
  ·
    refine ⟨38614207457241863601496411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51485609942989151468661881 38614207457241863601496411)
    ·
      refine ⟨57921311185862795402244617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38614207457241863601496411 57921311185862795402244617)
      ·
        refine ⟨43440983389397096551683463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57921311185862795402244617 43440983389397096551683463)
        ·
          refine ⟨65161475084095644827525195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43440983389397096551683463 65161475084095644827525195)
          ·
            refine ⟨97742212626143467241287793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65161475084095644827525195 97742212626143467241287793)
            ·
              refine ⟨73306659469607600430965845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97742212626143467241287793 73306659469607600430965845)
              ·
                refine ⟨859062415659464067550381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 73306659469607600430965845 859062415659464067550381)
                ·
                  refine ⟨322148405872299025331393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859062415659464067550381 322148405872299025331393)
                  ·
                    rfl

theorem cell21_1411609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_1411609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411609 prefixEnd_1411609 := by exact prefixLift 1411609
  have htrace : WordTrace (prefixWord ++ tailWord_1411609) baseStart_1411609 baseEnd_1411609 := by
    simpa [prefixWord, tailWord_1411609, baseEnd_1411609] using wordTrace_append hprefix tailTrace_1411609
  have hstable : (prefixWord ++ tailWord_1411609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411609).length < 2 ^ (prefixWord ++ tailWord_1411609).sum := by decide
  have hdescent : baseEnd_1411609 < baseStart_1411609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411688 : List Nat := [2, 1, 4, 3, 2, 2, 2, 5]
def baseStart_1411688 : Nat := 118140960795 + 1411688 * 2 ^ 59
def prefixEnd_1411688 : Nat := 4983230072969 + 3 ^ 40 * 1411688 * 2
def baseEnd_1411688 : Nat := 107388811582870814504855

theorem tailTrace_1411688 : CollatzResearch.WordTrace tailWord_1411688 prefixEnd_1411688 107388811582870814504855 := by
  unfold tailWord_1411688
  simp only [CollatzResearch.WordTrace]
  refine ⟨25744245654851473980393859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34325660873135298640525145 25744245654851473980393859)
  ·
    refine ⟨38616368482277210970590789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25744245654851473980393859 38616368482277210970590789)
    ·
      refine ⟨7240569090426977056985773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38616368482277210970590789 7240569090426977056985773)
      ·
        refine ⟨2715213408910116396369665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7240569090426977056985773 2715213408910116396369665)
        ·
          refine ⟨2036410056682587297277249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2715213408910116396369665 2036410056682587297277249)
          ·
            refine ⟨1527307542511940472957937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2036410056682587297277249 1527307542511940472957937)
            ·
              refine ⟨1145480656883955354718453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1527307542511940472957937 1145480656883955354718453)
              ·
                refine ⟨107388811582870814504855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1145480656883955354718453 107388811582870814504855)
                ·
                  rfl

theorem cell21_1411688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_1411688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411688 prefixEnd_1411688 := by exact prefixLift 1411688
  have htrace : WordTrace (prefixWord ++ tailWord_1411688) baseStart_1411688 baseEnd_1411688 := by
    simpa [prefixWord, tailWord_1411688, baseEnd_1411688] using wordTrace_append hprefix tailTrace_1411688
  have hstable : (prefixWord ++ tailWord_1411688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411688).length < 2 ^ (prefixWord ++ tailWord_1411688).sum := by decide
  have hdescent : baseEnd_1411688 < baseStart_1411688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411730 : List Nat := [3, 2, 3, 1, 2, 1, 1, 8]
def baseStart_1411730 : Nat := 118140960795 + 1411730 * 2 ^ 59
def prefixEnd_1411730 : Nat := 4983230072969 + 3 ^ 40 * 1411730 * 2
def baseEnd_1411730 : Nat := 107392006573609901271493

theorem tailTrace_1411730 : CollatzResearch.WordTrace tailWord_1411730 prefixEnd_1411730 107392006573609901271493 := by
  unfold tailWord_1411730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12872505793887697283454161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34326682117033859422544429 12872505793887697283454161)
  ·
    refine ⟨9654379345415772962590621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12872505793887697283454161 9654379345415772962590621)
    ·
      refine ⟨3620392254530914860971483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9654379345415772962590621 3620392254530914860971483)
      ·
        refine ⟨5430588381796372291457225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3620392254530914860971483 5430588381796372291457225)
        ·
          refine ⟨4072941286347279218592919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5430588381796372291457225 4072941286347279218592919)
          ·
            refine ⟨6109411929520918827889379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072941286347279218592919 6109411929520918827889379)
            ·
              refine ⟨9164117894281378241834069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6109411929520918827889379 9164117894281378241834069)
              ·
                refine ⟨107392006573609901271493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9164117894281378241834069 107392006573609901271493)
                ·
                  rfl

theorem cell21_1411730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_1411730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411730 prefixEnd_1411730 := by exact prefixLift 1411730
  have htrace : WordTrace (prefixWord ++ tailWord_1411730) baseStart_1411730 baseEnd_1411730 := by
    simpa [prefixWord, tailWord_1411730, baseEnd_1411730] using wordTrace_append hprefix tailTrace_1411730
  have hstable : (prefixWord ++ tailWord_1411730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411730).length < 2 ^ (prefixWord ++ tailWord_1411730).sum := by decide
  have hdescent : baseEnd_1411730 < baseStart_1411730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411775 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 4]
def baseStart_1411775 : Nat := 118140960795 + 1411775 * 2 ^ 59
def prefixEnd_1411775 : Nat := 4983230072969 + 3 ^ 40 * 1411775 * 2
def baseEnd_1411775 : Nat := 322186289333919625564387

theorem tailTrace_1411775 : CollatzResearch.WordTrace tailWord_1411775 prefixEnd_1411775 322186289333919625564387 := by
  unfold tailWord_1411775
  simp only [CollatzResearch.WordTrace]
  refine ⟨51491664460387761819204779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34327776306925174546136519 51491664460387761819204779)
  ·
    refine ⟨77237496690581642728807169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51491664460387761819204779 77237496690581642728807169)
    ·
      refine ⟨57928122517936232046605377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77237496690581642728807169 57928122517936232046605377)
      ·
        refine ⟨43446091888452174034954033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57928122517936232046605377 43446091888452174034954033)
        ·
          refine ⟨32584568916339130526215525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43446091888452174034954033 32584568916339130526215525)
          ·
            refine ⟨6109606671813586973665411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32584568916339130526215525 6109606671813586973665411)
            ·
              refine ⟨9164410007720380460498117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6109606671813586973665411 9164410007720380460498117)
              ·
                refine ⟨1718326876447571336343397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9164410007720380460498117 1718326876447571336343397)
                ·
                  refine ⟨322186289333919625564387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1718326876447571336343397 322186289333919625564387)
                  ·
                    rfl

theorem cell21_1411775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 4].length) (baseStart_1411775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411775 prefixEnd_1411775 := by exact prefixLift 1411775
  have htrace : WordTrace (prefixWord ++ tailWord_1411775) baseStart_1411775 baseEnd_1411775 := by
    simpa [prefixWord, tailWord_1411775, baseEnd_1411775] using wordTrace_append hprefix tailTrace_1411775
  have hstable : (prefixWord ++ tailWord_1411775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411775).length < 2 ^ (prefixWord ++ tailWord_1411775).sum := by decide
  have hdescent : baseEnd_1411775 < baseStart_1411775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411837 : List Nat := [1, 4, 1, 1, 1, 1, 3, 6, 3]
def baseStart_1411837 : Nat := 118140960795 + 1411837 * 2 ^ 59
def prefixEnd_1411837 : Nat := 4983230072969 + 3 ^ 40 * 1411837 * 2
def baseEnd_1411837 : Nat := 322200438578621295530927

theorem tailTrace_1411837 : CollatzResearch.WordTrace tailWord_1411837 prefixEnd_1411837 322200438578621295530927 := by
  unfold tailWord_1411837
  simp only [CollatzResearch.WordTrace]
  refine ⟨51493925786163146407961765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34329283857442097605307843 51493925786163146407961765)
  ·
    refine ⟨9655111084905589951492831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51493925786163146407961765 9655111084905589951492831)
    ·
      refine ⟨14482666627358384927239247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9655111084905589951492831 14482666627358384927239247)
      ·
        refine ⟨21723999941037577390858871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14482666627358384927239247 21723999941037577390858871)
        ·
          refine ⟨32585999911556366086288307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21723999941037577390858871 32585999911556366086288307)
          ·
            refine ⟨48878999867334549129432461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32585999911556366086288307 48878999867334549129432461)
            ·
              refine ⟨18329624950250455923537173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48878999867334549129432461 18329624950250455923537173)
              ·
                refine ⟨859201169542990121415805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18329624950250455923537173 859201169542990121415805)
                ·
                  refine ⟨322200438578621295530927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859201169542990121415805 322200438578621295530927)
                  ·
                    rfl

theorem cell21_1411837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_1411837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411837 prefixEnd_1411837 := by exact prefixLift 1411837
  have htrace : WordTrace (prefixWord ++ tailWord_1411837) baseStart_1411837 baseEnd_1411837 := by
    simpa [prefixWord, tailWord_1411837, baseEnd_1411837] using wordTrace_append hprefix tailTrace_1411837
  have hstable : (prefixWord ++ tailWord_1411837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411837).length < 2 ^ (prefixWord ++ tailWord_1411837).sum := by decide
  have hdescent : baseEnd_1411837 < baseStart_1411837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411902 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1411902 : Nat := 118140960795 + 1411902 * 2 ^ 59
def prefixEnd_1411902 : Nat := 4983230072969 + 3 ^ 40 * 1411902 * 2
def baseEnd_1411902 : Nat := 322215272464195626947461

theorem tailTrace_1411902 : CollatzResearch.WordTrace tailWord_1411902 prefixEnd_1411902 322215272464195626947461 := by
  unfold tailWord_1411902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437037066365957813634745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34330864353951775006051973 6437037066365957813634745)
  ·
    refine ⟨4827777799774468360226059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6437037066365957813634745 4827777799774468360226059)
    ·
      refine ⟨7241666699661702540339089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4827777799774468360226059 7241666699661702540339089)
      ·
        refine ⟨5431250024746276905254317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7241666699661702540339089 5431250024746276905254317)
        ·
          refine ⟨2036718759279853839470369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5431250024746276905254317 2036718759279853839470369)
          ·
            refine ⟨1527539069459890379602777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2036718759279853839470369 1527539069459890379602777)
            ·
              refine ⟨1145654302094917784702083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1527539069459890379602777 1145654302094917784702083)
              ·
                refine ⟨1718481453142376677053125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145654302094917784702083 1718481453142376677053125)
                ·
                  refine ⟨322215272464195626947461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1718481453142376677053125 322215272464195626947461)
                  ·
                    rfl

theorem cell21_1411902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1411902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411902 prefixEnd_1411902 := by exact prefixLift 1411902
  have htrace : WordTrace (prefixWord ++ tailWord_1411902) baseStart_1411902 baseEnd_1411902 := by
    simpa [prefixWord, tailWord_1411902, baseEnd_1411902] using wordTrace_append hprefix tailTrace_1411902
  have hstable : (prefixWord ++ tailWord_1411902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411902).length < 2 ^ (prefixWord ++ tailWord_1411902).sum := by decide
  have hdescent : baseEnd_1411902 < baseStart_1411902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411944 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_1411944 : Nat := 118140960795 + 1411944 * 2 ^ 59
def prefixEnd_1411944 : Nat := 4983230072969 + 3 ^ 40 * 1411944 * 2
def baseEnd_1411944 : Nat := 322224857436412887247375

theorem tailTrace_1411944 : CollatzResearch.WordTrace tailWord_1411944 prefixEnd_1411944 322224857436412887247375 := by
  unfold tailWord_1411944
  simp only [CollatzResearch.WordTrace]
  refine ⟨25748914198387751841053443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34331885597850335788071257 25748914198387751841053443)
  ·
    refine ⟨38623371297581627761580165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25748914198387751841053443 38623371297581627761580165)
    ·
      refine ⟨7241882118296555205296281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38623371297581627761580165 7241882118296555205296281)
      ·
        refine ⟨5431411588722416403972211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7241882118296555205296281 5431411588722416403972211)
        ·
          refine ⟨8147117383083624605958317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5431411588722416403972211 8147117383083624605958317)
          ·
            refine ⟨3055169018656359227234369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8147117383083624605958317 3055169018656359227234369)
            ·
              refine ⟨2291376763992269420425777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3055169018656359227234369 2291376763992269420425777)
              ·
                refine ⟨1718532572994202065319333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2291376763992269420425777 1718532572994202065319333)
                ·
                  refine ⟨322224857436412887247375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1718532572994202065319333 322224857436412887247375)
                  ·
                    rfl

theorem cell21_1411944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_1411944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411944 prefixEnd_1411944 := by exact prefixLift 1411944
  have htrace : WordTrace (prefixWord ++ tailWord_1411944) baseStart_1411944 baseEnd_1411944 := by
    simpa [prefixWord, tailWord_1411944, baseEnd_1411944] using wordTrace_append hprefix tailTrace_1411944
  have hstable : (prefixWord ++ tailWord_1411944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411944).length < 2 ^ (prefixWord ++ tailWord_1411944).sum := by decide
  have hdescent : baseEnd_1411944 < baseStart_1411944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411989 : List Nat := [1, 3, 2, 1, 1, 4, 1, 5, 3]
def baseStart_1411989 : Nat := 118140960795 + 1411989 * 2 ^ 59
def prefixEnd_1411989 : Nat := 4983230072969 + 3 ^ 40 * 1411989 * 2
def baseEnd_1411989 : Nat := 322235127049502808997283

theorem tailTrace_1411989 : CollatzResearch.WordTrace tailWord_1411989 prefixEnd_1411989 322235127049502808997283 := by
  unfold tailWord_1411989
  simp only [CollatzResearch.WordTrace]
  refine ⟨51499469681612476367495021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34332979787741650911663347 51499469681612476367495021)
  ·
    refine ⟨19312301130604678637810633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51499469681612476367495021 19312301130604678637810633)
    ·
      refine ⟨14484225847953508978357975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19312301130604678637810633 14484225847953508978357975)
      ·
        refine ⟨21726338771930263467536963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14484225847953508978357975 21726338771930263467536963)
        ·
          refine ⟨32589508157895395201305445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21726338771930263467536963 32589508157895395201305445)
          ·
            refine ⟨6110532779605386600244771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32589508157895395201305445 6110532779605386600244771)
            ·
              refine ⟨9165799169408079900367157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110532779605386600244771 9165799169408079900367157)
              ·
                refine ⟨859293672132007490659421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9165799169408079900367157 859293672132007490659421)
                ·
                  refine ⟨322235127049502808997283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859293672132007490659421 322235127049502808997283)
                  ·
                    rfl

theorem cell21_1411989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_1411989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1411989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1411989 prefixEnd_1411989 := by exact prefixLift 1411989
  have htrace : WordTrace (prefixWord ++ tailWord_1411989) baseStart_1411989 baseEnd_1411989 := by
    simpa [prefixWord, tailWord_1411989, baseEnd_1411989] using wordTrace_append hprefix tailTrace_1411989
  have hstable : (prefixWord ++ tailWord_1411989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411989).length < 2 ^ (prefixWord ++ tailWord_1411989).sum := by decide
  have hdescent : baseEnd_1411989 < baseStart_1411989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412003 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 4]
def baseStart_1412003 : Nat := 118140960795 + 1412003 * 2 ^ 59
def prefixEnd_1412003 : Nat := 4983230072969 + 3 ^ 40 * 1412003 * 2
def baseEnd_1412003 : Nat := 322238322040241895763921

theorem tailTrace_1412003 : CollatzResearch.WordTrace tailWord_1412003 prefixEnd_1412003 322238322040241895763921 := by
  unfold tailWord_1412003
  simp only [CollatzResearch.WordTrace]
  refine ⟨51499980303561756758504663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34333320202374504505669775 51499980303561756758504663)
  ·
    refine ⟨77249970455342635137756995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51499980303561756758504663 77249970455342635137756995)
    ·
      refine ⟨115874955683013952706635493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77249970455342635137756995 115874955683013952706635493)
      ·
        refine ⟨21726554190565116132494155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115874955683013952706635493 21726554190565116132494155)
        ·
          refine ⟨32589831285847674198741233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21726554190565116132494155 32589831285847674198741233)
          ·
            refine ⟨24442373464385755649055925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32589831285847674198741233 24442373464385755649055925)
            ·
              refine ⟨2291472512286164592098993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24442373464385755649055925 2291472512286164592098993)
              ·
                refine ⟨1718604384214623444074245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2291472512286164592098993 1718604384214623444074245)
                ·
                  refine ⟨322238322040241895763921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1718604384214623444074245 322238322040241895763921)
                  ·
                    rfl

theorem cell21_1412003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 4].length) (baseStart_1412003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412003 prefixEnd_1412003 := by exact prefixLift 1412003
  have htrace : WordTrace (prefixWord ++ tailWord_1412003) baseStart_1412003 baseEnd_1412003 := by
    simpa [prefixWord, tailWord_1412003, baseEnd_1412003] using wordTrace_append hprefix tailTrace_1412003
  have hstable : (prefixWord ++ tailWord_1412003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412003).length < 2 ^ (prefixWord ++ tailWord_1412003).sum := by decide
  have hdescent : baseEnd_1412003 < baseStart_1412003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412031 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 7]
def baseStart_1412031 : Nat := 118140960795 + 1412031 * 2 ^ 59
def prefixEnd_1412031 : Nat := 4983230072969 + 3 ^ 40 * 1412031 * 2
def baseEnd_1412031 : Nat := 322244712021720069297197

theorem tailTrace_1412031 : CollatzResearch.WordTrace tailWord_1412031 prefixEnd_1412031 322244712021720069297197 := by
  unfold tailWord_1412031
  simp only [CollatzResearch.WordTrace]
  refine ⟨51501001547460317540523947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34334001031640211693682631 51501001547460317540523947)
  ·
    refine ⟨77251502321190476310785921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51501001547460317540523947 77251502321190476310785921)
    ·
      refine ⟨57938626740892857233089441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77251502321190476310785921 57938626740892857233089441)
      ·
        refine ⟨43453970055669642924817081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57938626740892857233089441 43453970055669642924817081)
        ·
          refine ⟨32590477541752232193612811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43453970055669642924817081 32590477541752232193612811)
          ·
            refine ⟨48885716312628348290419217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32590477541752232193612811 48885716312628348290419217)
            ·
              refine ⟨36664287234471261217814413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48885716312628348290419217 36664287234471261217814413)
              ·
                refine ⟨13749107712926722956680405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36664287234471261217814413 13749107712926722956680405)
                ·
                  refine ⟨322244712021720069297197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13749107712926722956680405 322244712021720069297197)
                  ·
                    rfl

theorem cell21_1412031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_1412031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412031 prefixEnd_1412031 := by exact prefixLift 1412031
  have htrace : WordTrace (prefixWord ++ tailWord_1412031) baseStart_1412031 baseEnd_1412031 := by
    simpa [prefixWord, tailWord_1412031, baseEnd_1412031] using wordTrace_append hprefix tailTrace_1412031
  have hstable : (prefixWord ++ tailWord_1412031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412031).length < 2 ^ (prefixWord ++ tailWord_1412031).sum := by decide
  have hdescent : baseEnd_1412031 < baseStart_1412031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412079 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 4]
def baseStart_1412079 : Nat := 118140960795 + 1412079 * 2 ^ 59
def prefixEnd_1412079 : Nat := 4983230072969 + 3 ^ 40 * 1412079 * 2
def baseEnd_1412079 : Nat := 322255666275682652497099

theorem tailTrace_1412079 : CollatzResearch.WordTrace tailWord_1412079 prefixEnd_1412079 322255666275682652497099 := by
  unfold tailWord_1412079
  simp only [CollatzResearch.WordTrace]
  refine ⟨51502752251286421738271291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34335168167524281158847527 51502752251286421738271291)
  ·
    refine ⟨77254128376929632607406937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51502752251286421738271291 77254128376929632607406937)
    ·
      refine ⟨57940596282697224455555203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77254128376929632607406937 57940596282697224455555203)
      ·
        refine ⟨86910894424045836683332805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57940596282697224455555203 86910894424045836683332805)
        ·
          refine ⟨16295792704508594378124901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86910894424045836683332805 16295792704508594378124901)
          ·
            refine ⟨3055461132095361445898419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16295792704508594378124901 3055461132095361445898419)
            ·
              refine ⟨4583191698143042168847629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055461132095361445898419 4583191698143042168847629)
              ·
                refine ⟨1718696886803640813317861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4583191698143042168847629 1718696886803640813317861)
                ·
                  refine ⟨322255666275682652497099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1718696886803640813317861 322255666275682652497099)
                  ·
                    rfl

theorem cell21_1412079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 4].length) (baseStart_1412079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412079 prefixEnd_1412079 := by exact prefixLift 1412079
  have htrace : WordTrace (prefixWord ++ tailWord_1412079) baseStart_1412079 baseEnd_1412079 := by
    simpa [prefixWord, tailWord_1412079, baseEnd_1412079] using wordTrace_append hprefix tailTrace_1412079
  have hstable : (prefixWord ++ tailWord_1412079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412079).length < 2 ^ (prefixWord ++ tailWord_1412079).sum := by decide
  have hdescent : baseEnd_1412079 < baseStart_1412079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412158 : List Nat := [4, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_1412158 : Nat := 118140960795 + 1412158 * 2 ^ 59
def prefixEnd_1412158 : Nat := 4983230072969 + 3 ^ 40 * 1412158 * 2
def baseEnd_1412158 : Nat := 322273695151996070680271

theorem tailTrace_1412158 : CollatzResearch.WordTrace tailWord_1412158 prefixEnd_1412158 322273695151996070680271 := by
  unfold tailWord_1412158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6438204202250027278799641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34337089078666812153598085 6438204202250027278799641)
  ·
    refine ⟨4828653151687520459099731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6438204202250027278799641 4828653151687520459099731)
    ·
      refine ⟨7242979727531280688649597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4828653151687520459099731 7242979727531280688649597)
      ·
        refine ⟨2716117397824230258243599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7242979727531280688649597 2716117397824230258243599)
        ·
          refine ⟨4074176096736345387365399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716117397824230258243599 4074176096736345387365399)
          ·
            refine ⟨6111264145104518081048099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074176096736345387365399 6111264145104518081048099)
            ·
              refine ⟨9166896217656777121572149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111264145104518081048099 9166896217656777121572149)
              ·
                refine ⟨859396520405322855147389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9166896217656777121572149 859396520405322855147389)
                ·
                  refine ⟨322273695151996070680271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859396520405322855147389 322273695151996070680271)
                  ·
                    rfl

theorem cell21_1412158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_1412158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412158 prefixEnd_1412158 := by exact prefixLift 1412158
  have htrace : WordTrace (prefixWord ++ tailWord_1412158) baseStart_1412158 baseEnd_1412158 := by
    simpa [prefixWord, tailWord_1412158, baseEnd_1412158] using wordTrace_append hprefix tailTrace_1412158
  have hstable : (prefixWord ++ tailWord_1412158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412158).length < 2 ^ (prefixWord ++ tailWord_1412158).sum := by decide
  have hdescent : baseEnd_1412158 < baseStart_1412158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412234 : List Nat := [3, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_1412234 : Nat := 118140960795 + 1412234 * 2 ^ 59
def prefixEnd_1412234 : Nat := 4983230072969 + 3 ^ 40 * 1412234 * 2
def baseEnd_1412234 : Nat := 322291039387436827413449

theorem tailTrace_1412234 : CollatzResearch.WordTrace tailWord_1412234 prefixEnd_1412234 322291039387436827413449 := by
  unfold tailWord_1412234
  simp only [CollatzResearch.WordTrace]
  refine ⟨12877101391431220802540939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34338937043816588806775837 12877101391431220802540939)
  ·
    refine ⟨19315652087146831203811409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12877101391431220802540939 19315652087146831203811409)
    ·
      refine ⟨14486739065360123402858557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19315652087146831203811409 14486739065360123402858557)
      ·
        refine ⟨5432527149510046276071959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14486739065360123402858557 5432527149510046276071959)
        ·
          refine ⟨8148790724265069414107939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432527149510046276071959 8148790724265069414107939)
          ·
            refine ⟨12223186086397604121161909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8148790724265069414107939 12223186086397604121161909)
            ·
              refine ⟨1145923695599775386358929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12223186086397604121161909 1145923695599775386358929)
              ·
                refine ⟨859442771699831539769197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145923695599775386358929 859442771699831539769197)
                ·
                  refine ⟨322291039387436827413449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859442771699831539769197 322291039387436827413449)
                  ·
                    rfl

theorem cell21_1412234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_1412234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412234 prefixEnd_1412234 := by exact prefixLift 1412234
  have htrace : WordTrace (prefixWord ++ tailWord_1412234) baseStart_1412234 baseEnd_1412234 := by
    simpa [prefixWord, tailWord_1412234, baseEnd_1412234] using wordTrace_append hprefix tailTrace_1412234
  have hstable : (prefixWord ++ tailWord_1412234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412234).length < 2 ^ (prefixWord ++ tailWord_1412234).sum := by decide
  have hdescent : baseEnd_1412234 < baseStart_1412234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412248 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_1412248 : Nat := 118140960795 + 1412248 * 2 ^ 59
def prefixEnd_1412248 : Nat := 4983230072969 + 3 ^ 40 * 1412248 * 2
def baseEnd_1412248 : Nat := 322294234378175914180087

theorem tailTrace_1412248 : CollatzResearch.WordTrace tailWord_1412248 prefixEnd_1412248 322294234378175914180087 := by
  unfold tailWord_1412248
  simp only [CollatzResearch.WordTrace]
  refine ⟨25754458093837081800586699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34339277458449442400782265 25754458093837081800586699)
  ·
    refine ⟨38631687140755622700880049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25754458093837081800586699 38631687140755622700880049)
    ·
      refine ⟨28973765355566717025660037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38631687140755622700880049 28973765355566717025660037)
      ·
        refine ⟨5432581004168759442311257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28973765355566717025660037 5432581004168759442311257)
        ·
          refine ⟨4074435753126569581733443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5432581004168759442311257 4074435753126569581733443)
          ·
            refine ⟨6111653629689854372600165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074435753126569581733443 6111653629689854372600165)
            ·
              refine ⟨1145935055566847694862531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6111653629689854372600165 1145935055566847694862531)
              ·
                refine ⟨1718902583350271542293797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145935055566847694862531 1718902583350271542293797)
                ·
                  refine ⟨322294234378175914180087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1718902583350271542293797 322294234378175914180087)
                  ·
                    rfl

theorem cell21_1412248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_1412248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412248 prefixEnd_1412248 := by exact prefixLift 1412248
  have htrace : WordTrace (prefixWord ++ tailWord_1412248) baseStart_1412248 baseEnd_1412248 := by
    simpa [prefixWord, tailWord_1412248, baseEnd_1412248] using wordTrace_append hprefix tailTrace_1412248
  have hstable : (prefixWord ++ tailWord_1412248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412248).length < 2 ^ (prefixWord ++ tailWord_1412248).sum := by decide
  have hdescent : baseEnd_1412248 < baseStart_1412248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412259 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 5]
def baseStart_1412259 : Nat := 118140960795 + 1412259 * 2 ^ 59
def prefixEnd_1412259 : Nat := 4983230072969 + 3 ^ 40 * 1412259 * 2
def baseEnd_1412259 : Nat := 322296744728042339496731

theorem tailTrace_1412259 : CollatzResearch.WordTrace tailWord_1412259 prefixEnd_1412259 322296744728042339496731 := by
  unfold tailWord_1412259
  simp only [CollatzResearch.WordTrace]
  refine ⟨51509317390634312479823831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34339544927089541653215887 51509317390634312479823831)
  ·
    refine ⟨77263976085951468719735747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51509317390634312479823831 77263976085951468719735747)
    ·
      refine ⟨115895964128927203079603621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77263976085951468719735747 115895964128927203079603621)
      ·
        refine ⟨21730493274173850577425679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115895964128927203079603621 21730493274173850577425679)
        ·
          refine ⟨32595739911260775866138519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21730493274173850577425679 32595739911260775866138519)
          ·
            refine ⟨48893609866891163799207779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32595739911260775866138519 48893609866891163799207779)
            ·
              refine ⟨73340414800336745698811669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48893609866891163799207779 73340414800336745698811669)
              ·
                refine ⟨3437831943765784954631797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73340414800336745698811669 3437831943765784954631797)
                ·
                  refine ⟨322296744728042339496731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3437831943765784954631797 322296744728042339496731)
                  ·
                    rfl

theorem cell21_1412259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_1412259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412259 prefixEnd_1412259 := by exact prefixLift 1412259
  have htrace : WordTrace (prefixWord ++ tailWord_1412259) baseStart_1412259 baseEnd_1412259 := by
    simpa [prefixWord, tailWord_1412259, baseEnd_1412259] using wordTrace_append hprefix tailTrace_1412259
  have hstable : (prefixWord ++ tailWord_1412259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412259).length < 2 ^ (prefixWord ++ tailWord_1412259).sum := by decide
  have hdescent : baseEnd_1412259 < baseStart_1412259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412310 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1412310 : Nat := 118140960795 + 1412310 * 2 ^ 59
def prefixEnd_1412310 : Nat := 4983230072969 + 3 ^ 40 * 1412310 * 2
def baseEnd_1412310 : Nat := 322308383622877584146627

theorem tailTrace_1412310 : CollatzResearch.WordTrace tailWord_1412310 prefixEnd_1412310 322308383622877584146627 := by
  unfold tailWord_1412310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219448594590596761870649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34340785008966365459953589 3219448594590596761870649)
  ·
    refine ⟨2414586445942947571402987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3219448594590596761870649 2414586445942947571402987)
    ·
      refine ⟨3621879668914421357104481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414586445942947571402987 3621879668914421357104481)
      ·
        refine ⟨2716409751685816017828361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3621879668914421357104481 2716409751685816017828361)
        ·
          refine ⟨2037307313764362013371271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716409751685816017828361 2037307313764362013371271)
          ·
            refine ⟨3055960970646543020056907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037307313764362013371271 3055960970646543020056907)
            ·
              refine ⟨4583941455969814530085361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055960970646543020056907 4583941455969814530085361)
              ·
                refine ⟨3437956091977360897564021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4583941455969814530085361 3437956091977360897564021)
                ·
                  refine ⟨322308383622877584146627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3437956091977360897564021 322308383622877584146627)
                  ·
                    rfl

theorem cell21_1412310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1412310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412310 prefixEnd_1412310 := by exact prefixLift 1412310
  have htrace : WordTrace (prefixWord ++ tailWord_1412310) baseStart_1412310 baseEnd_1412310 := by
    simpa [prefixWord, tailWord_1412310, baseEnd_1412310] using wordTrace_append hprefix tailTrace_1412310
  have hstable : (prefixWord ++ tailWord_1412310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412310).length < 2 ^ (prefixWord ++ tailWord_1412310).sum := by decide
  have hdescent : baseEnd_1412310 < baseStart_1412310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412417 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 4]
def baseStart_1412417 : Nat := 118140960795 + 1412417 * 2 ^ 59
def prefixEnd_1412417 : Nat := 4983230072969 + 3 ^ 40 * 1412417 * 2
def baseEnd_1412417 : Nat := 322332802480669175863075

theorem tailTrace_1412417 : CollatzResearch.WordTrace tailWord_1412417 prefixEnd_1412417 322332802480669175863075 := by
  unfold tailWord_1412417
  simp only [CollatzResearch.WordTrace]
  refine ⟨51515080124061905464075505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34343386749374603642717003 51515080124061905464075505)
  ·
    refine ⟨38636310093046429098056629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51515080124061905464075505 38636310093046429098056629)
    ·
      refine ⟨3622154071223102727942809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38636310093046429098056629 3622154071223102727942809)
      ·
        refine ⟨2716615553417327045957107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3622154071223102727942809 2716615553417327045957107)
        ·
          refine ⟨4074923330125990568935661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716615553417327045957107 4074923330125990568935661)
          ·
            refine ⟨1528096248797246463350873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4074923330125990568935661 1528096248797246463350873)
            ·
              refine ⟨1146072186597934847513155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528096248797246463350873 1146072186597934847513155)
              ·
                refine ⟨1719108279896902271269733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146072186597934847513155 1719108279896902271269733)
                ·
                  refine ⟨322332802480669175863075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719108279896902271269733 322332802480669175863075)
                  ·
                    rfl

theorem cell21_1412417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_1412417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412417 prefixEnd_1412417 := by exact prefixLift 1412417
  have htrace : WordTrace (prefixWord ++ tailWord_1412417) baseStart_1412417 baseEnd_1412417 := by
    simpa [prefixWord, tailWord_1412417, baseEnd_1412417] using wordTrace_append hprefix tailTrace_1412417
  have hstable : (prefixWord ++ tailWord_1412417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412417).length < 2 ^ (prefixWord ++ tailWord_1412417).sum := by decide
  have hdescent : baseEnd_1412417 < baseStart_1412417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412456 : List Nat := [2, 1, 4, 2, 12]
def baseStart_1412456 : Nat := 118140960795 + 1412456 * 2 ^ 59
def prefixEnd_1412456 : Nat := 4983230072969 + 3 ^ 40 * 1412456 * 2
def baseEnd_1412456 : Nat := 3979527195210046601395

theorem tailTrace_1412456 : CollatzResearch.WordTrace tailWord_1412456 prefixEnd_1412456 3979527195210046601395 := by
  unfold tailWord_1412456
  simp only [CollatzResearch.WordTrace]
  refine ⟨25758251285460307562372611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34344335047280410083163481 25758251285460307562372611)
  ·
    refine ⟨38637376928190461343558917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25758251285460307562372611 38637376928190461343558917)
    ·
      refine ⟨7244508174035711501917297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38637376928190461343558917 7244508174035711501917297)
      ·
        refine ⟨5433381130526783626437973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7244508174035711501917297 5433381130526783626437973)
        ·
          refine ⟨3979527195210046601395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5433381130526783626437973 3979527195210046601395)
          ·
            rfl

theorem cell21_1412456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 12].length) (baseStart_1412456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412456 prefixEnd_1412456 := by exact prefixLift 1412456
  have htrace : WordTrace (prefixWord ++ tailWord_1412456) baseStart_1412456 baseEnd_1412456 := by
    simpa [prefixWord, tailWord_1412456, baseEnd_1412456] using wordTrace_append hprefix tailTrace_1412456
  have hstable : (prefixWord ++ tailWord_1412456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412456).length < 2 ^ (prefixWord ++ tailWord_1412456).sum := by decide
  have hdescent : baseEnd_1412456 < baseStart_1412456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412487 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 7]
def baseStart_1412487 : Nat := 118140960795 + 1412487 * 2 ^ 59
def prefixEnd_1412487 : Nat := 4983230072969 + 3 ^ 40 * 1412487 * 2
def baseEnd_1412487 : Nat := 322348777434364609696265

theorem tailTrace_1412487 : CollatzResearch.WordTrace tailWord_1412487 prefixEnd_1412487 322348777434364609696265 := by
  unfold tailWord_1412487
  simp only [CollatzResearch.WordTrace]
  refine ⟨51517633233808307419123715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34345088822538871612749143 51517633233808307419123715)
  ·
    refine ⟨77276449850712461128685573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51517633233808307419123715 77276449850712461128685573)
    ·
      refine ⟨14489334347008586461628545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77276449850712461128685573 14489334347008586461628545)
      ·
        refine ⟨10867000760256439846221409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14489334347008586461628545 10867000760256439846221409)
        ·
          refine ⟨8150250570192329884666057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10867000760256439846221409 8150250570192329884666057)
          ·
            refine ⟨6112687927644247413499543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8150250570192329884666057 6112687927644247413499543)
            ·
              refine ⟨9169031891466371120249315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112687927644247413499543 9169031891466371120249315)
              ·
                refine ⟨13753547837199556680373973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9169031891466371120249315 13753547837199556680373973)
                ·
                  refine ⟨322348777434364609696265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13753547837199556680373973 322348777434364609696265)
                  ·
                    rfl

theorem cell21_1412487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_1412487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412487 prefixEnd_1412487 := by exact prefixLift 1412487
  have htrace : WordTrace (prefixWord ++ tailWord_1412487) baseStart_1412487 baseEnd_1412487 := by
    simpa [prefixWord, tailWord_1412487, baseEnd_1412487] using wordTrace_append hprefix tailTrace_1412487
  have hstable : (prefixWord ++ tailWord_1412487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412487).length < 2 ^ (prefixWord ++ tailWord_1412487).sum := by decide
  have hdescent : baseEnd_1412487 < baseStart_1412487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412510 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1412510 : Nat := 118140960795 + 1412510 * 2 ^ 59
def prefixEnd_1412510 : Nat := 4983230072969 + 3 ^ 40 * 1412510 * 2
def baseEnd_1412510 : Nat := 322354026347721680812885

theorem tailTrace_1412510 : CollatzResearch.WordTrace tailWord_1412510 prefixEnd_1412510 322354026347721680812885 := by
  unfold tailWord_1412510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6439809014090622793401373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34345648075149988231473989 6439809014090622793401373)
  ·
    refine ⟨2414928380283983547525515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6439809014090622793401373 2414928380283983547525515)
    ·
      refine ⟨3622392570425975321288273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414928380283983547525515 3622392570425975321288273)
      ·
        refine ⟨2716794427819481490966205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3622392570425975321288273 2716794427819481490966205)
        ·
          refine ⟨1018797910432305559112327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2716794427819481490966205 1018797910432305559112327)
          ·
            refine ⟨1528196865648458338668491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018797910432305559112327 1528196865648458338668491)
            ·
              refine ⟨2292295298472687508002737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528196865648458338668491 2292295298472687508002737)
              ·
                refine ⟨1719221473854515631002053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292295298472687508002737 1719221473854515631002053)
                ·
                  refine ⟨322354026347721680812885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719221473854515631002053 322354026347721680812885)
                  ·
                    rfl

theorem cell21_1412510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1412510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412510 prefixEnd_1412510 := by exact prefixLift 1412510
  have htrace : WordTrace (prefixWord ++ tailWord_1412510) baseStart_1412510 baseEnd_1412510 := by
    simpa [prefixWord, tailWord_1412510, baseEnd_1412510] using wordTrace_append hprefix tailTrace_1412510
  have hstable : (prefixWord ++ tailWord_1412510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412510).length < 2 ^ (prefixWord ++ tailWord_1412510).sum := by decide
  have hdescent : baseEnd_1412510 < baseStart_1412510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412535 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 4]
def baseStart_1412535 : Nat := 118140960795 + 1412535 * 2 ^ 59
def prefixEnd_1412535 : Nat := 4983230072969 + 3 ^ 40 * 1412535 * 2
def baseEnd_1412535 : Nat := 322359731688327192896167

theorem tailTrace_1412535 : CollatzResearch.WordTrace tailWord_1412535 prefixEnd_1412535 322359731688327192896167 := by
  unfold tailWord_1412535
  simp only [CollatzResearch.WordTrace]
  refine ⟨51519383937634411616871059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34346255958422941077914039 51519383937634411616871059)
  ·
    refine ⟨77279075906451617425306589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51519383937634411616871059 77279075906451617425306589)
    ·
      refine ⟨28979653464919356534489971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77279075906451617425306589 28979653464919356534489971)
      ·
        refine ⟨43469480197379034801734957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28979653464919356534489971 43469480197379034801734957)
        ·
          refine ⟨16301055074017138050650609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43469480197379034801734957 16301055074017138050650609)
          ·
            refine ⟨12225791305512853537987957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16301055074017138050650609 12225791305512853537987957)
            ·
              refine ⟨1146167934891830019186371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12225791305512853537987957 1146167934891830019186371)
              ·
                refine ⟨1719251902337745028779557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146167934891830019186371 1719251902337745028779557)
                ·
                  refine ⟨322359731688327192896167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719251902337745028779557 322359731688327192896167)
                  ·
                    rfl

theorem cell21_1412535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 4].length) (baseStart_1412535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412535 prefixEnd_1412535 := by exact prefixLift 1412535
  have htrace : WordTrace (prefixWord ++ tailWord_1412535) baseStart_1412535 baseEnd_1412535 := by
    simpa [prefixWord, tailWord_1412535, baseEnd_1412535] using wordTrace_append hprefix tailTrace_1412535
  have hstable : (prefixWord ++ tailWord_1412535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412535).length < 2 ^ (prefixWord ++ tailWord_1412535).sum := by decide
  have hdescent : baseEnd_1412535 < baseStart_1412535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412566 : List Nat := [5, 2, 1, 1, 1, 4, 7]
def baseStart_1412566 : Nat := 118140960795 + 1412566 * 2 ^ 59
def prefixEnd_1412566 : Nat := 4983230072969 + 3 ^ 40 * 1412566 * 2
def baseEnd_1412566 : Nat := 35818534034519780875493

theorem tailTrace_1412566 : CollatzResearch.WordTrace tailWord_1412566 prefixEnd_1412566 35818534034519780875493 := by
  unfold tailWord_1412566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220032162532631494453097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34347009733681402607499701 3220032162532631494453097)
  ·
    refine ⟨2415024121899473620839823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3220032162532631494453097 2415024121899473620839823)
    ·
      refine ⟨3622536182849210431259735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415024121899473620839823 3622536182849210431259735)
      ·
        refine ⟨5433804274273815646889603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622536182849210431259735 5433804274273815646889603)
        ·
          refine ⟨8150706411410723470334405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433804274273815646889603 8150706411410723470334405)
          ·
            refine ⟨1528257452139510650687701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8150706411410723470334405 1528257452139510650687701)
            ·
              refine ⟨35818534034519780875493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1528257452139510650687701 35818534034519780875493)
              ·
                rfl

theorem cell21_1412566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 7].length) (baseStart_1412566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412566 prefixEnd_1412566 := by exact prefixLift 1412566
  have htrace : WordTrace (prefixWord ++ tailWord_1412566) baseStart_1412566 baseEnd_1412566 := by
    simpa [prefixWord, tailWord_1412566, baseEnd_1412566] using wordTrace_append hprefix tailTrace_1412566
  have hstable : (prefixWord ++ tailWord_1412566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412566).length < 2 ^ (prefixWord ++ tailWord_1412566).sum := by decide
  have hdescent : baseEnd_1412566 < baseStart_1412566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412580 : List Nat := [2, 3, 1, 1, 1, 1, 1, 8, 3]
def baseStart_1412580 : Nat := 118140960795 + 1412580 * 2 ^ 59
def prefixEnd_1412580 : Nat := 4983230072969 + 3 ^ 40 * 1412580 * 2
def baseEnd_1412580 : Nat := 322370001301417114646075

theorem tailTrace_1412580 : CollatzResearch.WordTrace tailWord_1412580 prefixEnd_1412580 322370001301417114646075 := by
  unfold tailWord_1412580
  simp only [CollatzResearch.WordTrace]
  refine ⟨25760512611235692151129597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34347350148314256201506129 25760512611235692151129597)
  ·
    refine ⟨9660192229213384556673599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25760512611235692151129597 9660192229213384556673599)
    ·
      refine ⟨14490288343820076835010399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9660192229213384556673599 14490288343820076835010399)
      ·
        refine ⟨21735432515730115252515599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14490288343820076835010399 21735432515730115252515599)
        ·
          refine ⟨32603148773595172878773399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21735432515730115252515599 32603148773595172878773399)
          ·
            refine ⟨48904723160392759318160099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32603148773595172878773399 48904723160392759318160099)
            ·
              refine ⟨73357084740589138977240149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48904723160392759318160099 73357084740589138977240149)
              ·
                refine ⟨859653336803778972389533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 73357084740589138977240149 859653336803778972389533)
                ·
                  refine ⟨322370001301417114646075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859653336803778972389533 322370001301417114646075)
                  ·
                    rfl

theorem cell21_1412580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_1412580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412580 prefixEnd_1412580 := by exact prefixLift 1412580
  have htrace : WordTrace (prefixWord ++ tailWord_1412580) baseStart_1412580 baseEnd_1412580 := by
    simpa [prefixWord, tailWord_1412580, baseEnd_1412580] using wordTrace_append hprefix tailTrace_1412580
  have hstable : (prefixWord ++ tailWord_1412580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412580).length < 2 ^ (prefixWord ++ tailWord_1412580).sum := by decide
  have hdescent : baseEnd_1412580 < baseStart_1412580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412673 : List Nat := [1, 2, 5, 1, 1, 1, 4, 3, 3]
def baseStart_1412673 : Nat := 118140960795 + 1412673 * 2 ^ 59
def prefixEnd_1412673 : Nat := 4983230072969 + 3 ^ 40 * 1412673 * 2
def baseEnd_1412673 : Nat := 322391225168469619595885

theorem tailTrace_1412673 : CollatzResearch.WordTrace tailWord_1412673 prefixEnd_1412673 322391225168469619595885 := by
  unfold tailWord_1412673
  simp only [CollatzResearch.WordTrace]
  refine ⟨51524417211134461185394673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34349611474089640790263115 51524417211134461185394673)
  ·
    refine ⟨38643312908350845889046005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51524417211134461185394673 38643312908350845889046005)
    ·
      refine ⟨3622810585157891802098063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38643312908350845889046005 3622810585157891802098063)
      ·
        refine ⟨5434215877736837703147095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622810585157891802098063 5434215877736837703147095)
        ·
          refine ⟨8151323816605256554720643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5434215877736837703147095 8151323816605256554720643)
          ·
            refine ⟨12226985724907884832080965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151323816605256554720643 12226985724907884832080965)
            ·
              refine ⟨2292559823420228406015181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12226985724907884832080965 2292559823420228406015181)
              ·
                refine ⟨859709933782585652255693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2292559823420228406015181 859709933782585652255693)
                ·
                  refine ⟨322391225168469619595885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859709933782585652255693 322391225168469619595885)
                  ·
                    rfl

theorem cell21_1412673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_1412673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412673 prefixEnd_1412673 := by exact prefixLift 1412673
  have htrace : WordTrace (prefixWord ++ tailWord_1412673) baseStart_1412673 baseEnd_1412673 := by
    simpa [prefixWord, tailWord_1412673, baseEnd_1412673] using wordTrace_append hprefix tailTrace_1412673
  have hstable : (prefixWord ++ tailWord_1412673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412673).length < 2 ^ (prefixWord ++ tailWord_1412673).sum := by decide
  have hdescent : baseEnd_1412673 < baseStart_1412673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412684 : List Nat := [2, 2, 1, 3, 1, 4, 8]
def baseStart_1412684 : Nat := 118140960795 + 1412684 * 2 ^ 59
def prefixEnd_1412684 : Nat := 4983230072969 + 3 ^ 40 * 1412684 * 2
def baseEnd_1412684 : Nat := 35821526168704004990281

theorem tailTrace_1412684 : CollatzResearch.WordTrace tailWord_1412684 prefixEnd_1412684 35821526168704004990281 := by
  unfold tailWord_1412684
  simp only [CollatzResearch.WordTrace]
  refine ⟨25762409207047305032022553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34349878942729740042696737 25762409207047305032022553)
  ·
    refine ⟨19321806905285478774016915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25762409207047305032022553 19321806905285478774016915)
    ·
      refine ⟨28982710357928218161025373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19321806905285478774016915 28982710357928218161025373)
      ·
        refine ⟨10868516384223081810384515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28982710357928218161025373 10868516384223081810384515)
        ·
          refine ⟨16302774576334622715576773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10868516384223081810384515 16302774576334622715576773)
          ·
            refine ⟨3056770233062741759170645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16302774576334622715576773 3056770233062741759170645)
            ·
              refine ⟨35821526168704004990281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3056770233062741759170645 35821526168704004990281)
              ·
                rfl

theorem cell21_1412684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 8].length) (baseStart_1412684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412684 prefixEnd_1412684 := by exact prefixLift 1412684
  have htrace : WordTrace (prefixWord ++ tailWord_1412684) baseStart_1412684 baseEnd_1412684 := by
    simpa [prefixWord, tailWord_1412684, baseEnd_1412684] using wordTrace_append hprefix tailTrace_1412684
  have hstable : (prefixWord ++ tailWord_1412684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412684).length < 2 ^ (prefixWord ++ tailWord_1412684).sum := by decide
  have hdescent : baseEnd_1412684 < baseStart_1412684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412729 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 8]
def baseStart_1412729 : Nat := 118140960795 + 1412729 * 2 ^ 59
def prefixEnd_1412729 : Nat := 4983230072969 + 3 ^ 40 * 1412729 * 2
def baseEnd_1412729 : Nat := 322404005131425966662437

theorem tailTrace_1412729 : CollatzResearch.WordTrace tailWord_1412729 prefixEnd_1412729 322404005131425966662437 := by
  unfold tailWord_1412729
  simp only [CollatzResearch.WordTrace]
  refine ⟨51526459698931582749433241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34350973132621055166288827 51526459698931582749433241)
  ·
    refine ⟨38644844774198687062074931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51526459698931582749433241 38644844774198687062074931)
    ·
      refine ⟨57967267161298030593112397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38644844774198687062074931 57967267161298030593112397)
      ·
        refine ⟨21737725185486761472417149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57967267161298030593112397 21737725185486761472417149)
        ·
          refine ⟨8151646944557535552156431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21737725185486761472417149 8151646944557535552156431)
          ·
            refine ⟨12227470416836303328234647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151646944557535552156431 12227470416836303328234647)
            ·
              refine ⟨18341205625254454992351971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12227470416836303328234647 18341205625254454992351971)
              ·
                refine ⟨27511808437881682488527957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18341205625254454992351971 27511808437881682488527957)
                ·
                  refine ⟨322404005131425966662437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27511808437881682488527957 322404005131425966662437)
                  ·
                    rfl

theorem cell21_1412729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_1412729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412729 prefixEnd_1412729 := by exact prefixLift 1412729
  have htrace : WordTrace (prefixWord ++ tailWord_1412729) baseStart_1412729 baseEnd_1412729 := by
    simpa [prefixWord, tailWord_1412729, baseEnd_1412729] using wordTrace_append hprefix tailTrace_1412729
  have hstable : (prefixWord ++ tailWord_1412729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412729).length < 2 ^ (prefixWord ++ tailWord_1412729).sum := by decide
  have hdescent : baseEnd_1412729 < baseStart_1412729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412746 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_1412746 : Nat := 118140960795 + 1412746 * 2 ^ 59
def prefixEnd_1412746 : Nat := 4983230072969 + 3 ^ 40 * 1412746 * 2
def baseEnd_1412746 : Nat := 322407884763037714879069

theorem tailTrace_1412746 : CollatzResearch.WordTrace tailWord_1412746 prefixEnd_1412746 322407884763037714879069 := by
  unfold tailWord_1412746
  simp only [CollatzResearch.WordTrace]
  refine ⟨12881769934967498663200523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34351386493246663101868061 12881769934967498663200523)
  ·
    refine ⟨19322654902451247994800785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12881769934967498663200523 19322654902451247994800785)
    ·
      refine ⟨14491991176838435996100589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19322654902451247994800785 14491991176838435996100589)
      ·
        refine ⟨5434496691314413498537721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14491991176838435996100589 5434496691314413498537721)
        ·
          refine ⟨4075872518485810123903291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5434496691314413498537721 4075872518485810123903291)
          ·
            refine ⟨6113808777728715185854937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075872518485810123903291 6113808777728715185854937)
            ·
              refine ⟨4585356583296536389391203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6113808777728715185854937 4585356583296536389391203)
              ·
                refine ⟨6878034874944804584086805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4585356583296536389391203 6878034874944804584086805)
                ·
                  refine ⟨322407884763037714879069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6878034874944804584086805 322407884763037714879069)
                  ·
                    rfl

theorem cell21_1412746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_1412746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412746 prefixEnd_1412746 := by exact prefixLift 1412746
  have htrace : WordTrace (prefixWord ++ tailWord_1412746) baseStart_1412746 baseEnd_1412746 := by
    simpa [prefixWord, tailWord_1412746, baseEnd_1412746] using wordTrace_append hprefix tailTrace_1412746
  have hstable : (prefixWord ++ tailWord_1412746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412746).length < 2 ^ (prefixWord ++ tailWord_1412746).sum := by decide
  have hdescent : baseEnd_1412746 < baseStart_1412746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412760 : List Nat := [2, 1, 2, 4, 1, 2, 1, 8]
def baseStart_1412760 : Nat := 118140960795 + 1412760 * 2 ^ 59
def prefixEnd_1412760 : Nat := 4983230072969 + 3 ^ 40 * 1412760 * 2
def baseEnd_1412760 : Nat := 107470359917925600548569

theorem tailTrace_1412760 : CollatzResearch.WordTrace tailWord_1412760 prefixEnd_1412760 107470359917925600548569 := by
  unfold tailWord_1412760
  simp only [CollatzResearch.WordTrace]
  refine ⟨25763795180909637521905867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34351726907879516695874489 25763795180909637521905867)
  ·
    refine ⟨38645692771364456282858801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25763795180909637521905867 38645692771364456282858801)
    ·
      refine ⟨28984269578523342212144101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38645692771364456282858801 28984269578523342212144101)
      ·
        refine ⟨5434550545973126664777019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28984269578523342212144101 5434550545973126664777019)
        ·
          refine ⟨8151825818959689997165529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5434550545973126664777019 8151825818959689997165529)
          ·
            refine ⟨6113869364219767497874147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8151825818959689997165529 6113869364219767497874147)
            ·
              refine ⟨9170804046329651246811221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113869364219767497874147 9170804046329651246811221)
              ·
                refine ⟨107470359917925600548569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9170804046329651246811221 107470359917925600548569)
                ·
                  rfl

theorem cell21_1412760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_1412760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412760 prefixEnd_1412760 := by exact prefixLift 1412760
  have htrace : WordTrace (prefixWord ++ tailWord_1412760) baseStart_1412760 baseEnd_1412760 := by
    simpa [prefixWord, tailWord_1412760, baseEnd_1412760] using wordTrace_append hprefix tailTrace_1412760
  have hstable : (prefixWord ++ tailWord_1412760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412760).length < 2 ^ (prefixWord ++ tailWord_1412760).sum := by decide
  have hdescent : baseEnd_1412760 < baseStart_1412760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412808 : List Nat := [2, 1, 3, 1, 2, 2, 3, 4, 3]
def baseStart_1412808 : Nat := 118140960795 + 1412808 * 2 ^ 59
def prefixEnd_1412808 : Nat := 4983230072969 + 3 ^ 40 * 1412808 * 2
def baseEnd_1412808 : Nat := 322422034007739384845609

theorem tailTrace_1412808 : CollatzResearch.WordTrace tailWord_1412808 prefixEnd_1412808 322422034007739384845609 := by
  unfold tailWord_1412808
  simp only [CollatzResearch.WordTrace]
  refine ⟨25764670532822689620779539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34352894043763586161039385 25764670532822689620779539)
  ·
    refine ⟨38647005799234034431169309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25764670532822689620779539 38647005799234034431169309)
    ·
      refine ⟨14492627174712762911688491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38647005799234034431169309 14492627174712762911688491)
      ·
        refine ⟨21738940762069144367532737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14492627174712762911688491 21738940762069144367532737)
        ·
          refine ⟨16304205571551858275649553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21738940762069144367532737 16304205571551858275649553)
          ·
            refine ⟨12228154178663893706737165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16304205571551858275649553 12228154178663893706737165)
            ·
              refine ⟨4585557816998960140026437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12228154178663893706737165 4585557816998960140026437)
              ·
                refine ⟨859792090687305026254957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4585557816998960140026437 859792090687305026254957)
                ·
                  refine ⟨322422034007739384845609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859792090687305026254957 322422034007739384845609)
                  ·
                    rfl

theorem cell21_1412808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_1412808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412808 prefixEnd_1412808 := by exact prefixLift 1412808
  have htrace : WordTrace (prefixWord ++ tailWord_1412808) baseStart_1412808 baseEnd_1412808 := by
    simpa [prefixWord, tailWord_1412808, baseEnd_1412808] using wordTrace_append hprefix tailTrace_1412808
  have hstable : (prefixWord ++ tailWord_1412808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412808).length < 2 ^ (prefixWord ++ tailWord_1412808).sum := by decide
  have hdescent : baseEnd_1412808 < baseStart_1412808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412901 : List Nat := [1, 3, 1, 2, 3, 4, 1, 3, 3]
def baseStart_1412901 : Nat := 118140960795 + 1412901 * 2 ^ 59
def prefixEnd_1412901 : Nat := 4983230072969 + 3 ^ 40 * 1412901 * 2
def baseEnd_1412901 : Nat := 322443257874791889795419

theorem tailTrace_1412901 : CollatzResearch.WordTrace tailWord_1412901 prefixEnd_1412901 322443257874791889795419 := by
  unfold tailWord_1412901
  simp only [CollatzResearch.WordTrace]
  refine ⟨51532733054308456124694557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34355155369538970749796371 51532733054308456124694557)
  ·
    refine ⟨19324774895365671046760459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51532733054308456124694557 19324774895365671046760459)
    ·
      refine ⟨28987162343048506570140689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19324774895365671046760459 28987162343048506570140689)
      ·
        refine ⟨21740371757286379927605517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28987162343048506570140689 21740371757286379927605517)
        ·
          refine ⟨8152639408982392472852069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21740371757286379927605517 8152639408982392472852069)
          ·
            refine ⟨1528619889184198588659763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8152639408982392472852069 1528619889184198588659763)
            ·
              refine ⟨2292929833776297882989645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528619889184198588659763 2292929833776297882989645)
              ·
                refine ⟨859848687666111706121117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2292929833776297882989645 859848687666111706121117)
                ·
                  refine ⟨322443257874791889795419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859848687666111706121117 322443257874791889795419)
                  ·
                    rfl

theorem cell21_1412901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_1412901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1412901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1412901 prefixEnd_1412901 := by exact prefixLift 1412901
  have htrace : WordTrace (prefixWord ++ tailWord_1412901) baseStart_1412901 baseEnd_1412901 := by
    simpa [prefixWord, tailWord_1412901, baseEnd_1412901] using wordTrace_append hprefix tailTrace_1412901
  have hstable : (prefixWord ++ tailWord_1412901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412901).length < 2 ^ (prefixWord ++ tailWord_1412901).sum := by decide
  have hdescent : baseEnd_1412901 < baseStart_1412901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413022 : List Nat := [4, 3, 1, 3, 1, 1, 8]
def baseStart_1413022 : Nat := 118140960795 + 1413022 * 2 ^ 59
def prefixEnd_1413022 : Nat := 4983230072969 + 3 ^ 40 * 1413022 * 2
def baseEnd_1413022 : Nat := 35830096858146952030945

theorem tailTrace_1413022 : CollatzResearch.WordTrace tailWord_1413022 prefixEnd_1413022 35830096858146952030945 := by
  unfold tailWord_1413022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6442143285858761723731165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34358097524580062526566213 6442143285858761723731165)
  ·
    refine ⟨2415803732197035646399187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6442143285858761723731165 2415803732197035646399187)
    ·
      refine ⟨3623705598295553469598781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415803732197035646399187 3623705598295553469598781)
      ·
        refine ⟨1358889599360832551099543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3623705598295553469598781 1358889599360832551099543)
        ·
          refine ⟨2038334399041248826649315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358889599360832551099543 2038334399041248826649315)
          ·
            refine ⟨3057501598561873239973973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038334399041248826649315 3057501598561873239973973)
            ·
              refine ⟨35830096858146952030945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3057501598561873239973973 35830096858146952030945)
              ·
                rfl

theorem cell21_1413022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 8].length) (baseStart_1413022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413022 prefixEnd_1413022 := by exact prefixLift 1413022
  have htrace : WordTrace (prefixWord ++ tailWord_1413022) baseStart_1413022 baseEnd_1413022 := by
    simpa [prefixWord, tailWord_1413022, baseEnd_1413022] using wordTrace_append hprefix tailTrace_1413022
  have hstable : (prefixWord ++ tailWord_1413022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413022).length < 2 ^ (prefixWord ++ tailWord_1413022).sum := by decide
  have hdescent : baseEnd_1413022 < baseStart_1413022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413033 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 4]
def baseStart_1413033 : Nat := 118140960795 + 1413033 * 2 ^ 59
def prefixEnd_1413033 : Nat := 4983230072969 + 3 ^ 40 * 1413033 * 2
def baseEnd_1413033 : Nat := 322473382073188993595149

theorem tailTrace_1413033 : CollatzResearch.WordTrace tailWord_1413033 prefixEnd_1413033 322473382073188993595149 := by
  unfold tailWord_1413033
  simp only [CollatzResearch.WordTrace]
  refine ⟨51537547489830242668499753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34358364993220161778999835 51537547489830242668499753)
  ·
    refine ⟨38653160617372682001374815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51537547489830242668499753 38653160617372682001374815)
    ·
      refine ⟨57979740926059023002062223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38653160617372682001374815 57979740926059023002062223)
      ·
        refine ⟨86969611389088534503093335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57979740926059023002062223 86969611389088534503093335)
        ·
          refine ⟨130454417083632801754640003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86969611389088534503093335 130454417083632801754640003)
          ·
            refine ⟨195681625625449202631960005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130454417083632801754640003 195681625625449202631960005)
            ·
              refine ⟨36690304804771725493492501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195681625625449202631960005 36690304804771725493492501)
              ·
                refine ⟨1719858037723674632507461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36690304804771725493492501 1719858037723674632507461)
                ·
                  refine ⟨322473382073188993595149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719858037723674632507461 322473382073188993595149)
                  ·
                    rfl

theorem cell21_1413033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_1413033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413033 prefixEnd_1413033 := by exact prefixLift 1413033
  have htrace : WordTrace (prefixWord ++ tailWord_1413033) baseStart_1413033 baseEnd_1413033 := by
    simpa [prefixWord, tailWord_1413033, baseEnd_1413033] using wordTrace_append hprefix tailTrace_1413033
  have hstable : (prefixWord ++ tailWord_1413033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413033).length < 2 ^ (prefixWord ++ tailWord_1413033).sum := by decide
  have hdescent : baseEnd_1413033 < baseStart_1413033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413047 : List Nat := [1, 1, 3, 1, 3, 1, 1, 10]
def baseStart_1413047 : Nat := 118140960795 + 1413047 * 2 ^ 59
def prefixEnd_1413047 : Nat := 4983230072969 + 3 ^ 40 * 1413047 * 2
def baseEnd_1413047 : Nat := 107492192354642693453929

theorem tailTrace_1413047 : CollatzResearch.WordTrace tailWord_1413047 prefixEnd_1413047 107492192354642693453929 := by
  unfold tailWord_1413047
  simp only [CollatzResearch.WordTrace]
  refine ⟨51538058111779523059509395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34358705407853015373006263 51538058111779523059509395)
  ·
    refine ⟨77307087167669284589264093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51538058111779523059509395 77307087167669284589264093)
    ·
      refine ⟨28990157687875981720974035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77307087167669284589264093 28990157687875981720974035)
      ·
        refine ⟨43485236531813972581461053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28990157687875981720974035 43485236531813972581461053)
        ·
          refine ⟨16306963699430239718047895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43485236531813972581461053 16306963699430239718047895)
          ·
            refine ⟨24460445549145359577071843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16306963699430239718047895 24460445549145359577071843)
            ·
              refine ⟨36690668323718039365607765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24460445549145359577071843 36690668323718039365607765)
              ·
                refine ⟨107492192354642693453929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36690668323718039365607765 107492192354642693453929)
                ·
                  rfl

theorem cell21_1413047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 10].length) (baseStart_1413047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413047 prefixEnd_1413047 := by exact prefixLift 1413047
  have htrace : WordTrace (prefixWord ++ tailWord_1413047) baseStart_1413047 baseEnd_1413047 := by
    simpa [prefixWord, tailWord_1413047, baseEnd_1413047] using wordTrace_append hprefix tailTrace_1413047
  have hstable : (prefixWord ++ tailWord_1413047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413047).length < 2 ^ (prefixWord ++ tailWord_1413047).sum := by decide
  have hdescent : baseEnd_1413047 < baseStart_1413047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413064 : List Nat := [2, 1, 3, 1, 4, 2, 1, 7]
def baseStart_1413064 : Nat := 118140960795 + 1413064 * 2 ^ 59
def prefixEnd_1413064 : Nat := 4983230072969 + 3 ^ 40 * 1413064 * 2
def baseEnd_1413064 : Nat := 107493485565179942859473

theorem tailTrace_1413064 : CollatzResearch.WordTrace tailWord_1413064 prefixEnd_1413064 107493485565179942859473 := by
  unfold tailWord_1413064
  simp only [CollatzResearch.WordTrace]
  refine ⟨25769339076358967481439123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34359118768478623308585497 25769339076358967481439123)
  ·
    refine ⟨38654008614538451222158685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25769339076358967481439123 38654008614538451222158685)
    ·
      refine ⟨14495253230451919208309507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38654008614538451222158685 14495253230451919208309507)
      ·
        refine ⟨21742879845677878812464261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14495253230451919208309507 21742879845677878812464261)
        ·
          refine ⟨4076789971064602277337049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21742879845677878812464261 4076789971064602277337049)
          ·
            refine ⟨3057592478298451708002787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4076789971064602277337049 3057592478298451708002787)
            ·
              refine ⟨4586388717447677562004181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057592478298451708002787 4586388717447677562004181)
              ·
                refine ⟨107493485565179942859473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4586388717447677562004181 107493485565179942859473)
                ·
                  rfl

theorem cell21_1413064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_1413064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413064 prefixEnd_1413064 := by exact prefixLift 1413064
  have htrace : WordTrace (prefixWord ++ tailWord_1413064) baseStart_1413064 baseEnd_1413064 := by
    simpa [prefixWord, tailWord_1413064, baseEnd_1413064] using wordTrace_append hprefix tailTrace_1413064
  have hstable : (prefixWord ++ tailWord_1413064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413064).length < 2 ^ (prefixWord ++ tailWord_1413064).sum := by decide
  have hdescent : baseEnd_1413064 < baseStart_1413064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413081 : List Nat := [1, 2, 1, 2, 7, 1, 7]
def baseStart_1413081 : Nat := 118140960795 + 1413081 * 2 ^ 59
def prefixEnd_1413081 : Nat := 4983230072969 + 3 ^ 40 * 1413081 * 2
def baseEnd_1413081 : Nat := 35831592925239064088339

theorem tailTrace_1413081 : CollatzResearch.WordTrace tailWord_1413081 prefixEnd_1413081 35831592925239064088339 := by
  unfold tailWord_1413081
  simp only [CollatzResearch.WordTrace]
  refine ⟨51539298193656346866247097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34359532129104231244164731 51539298193656346866247097)
  ·
    refine ⟨38654473645242260149685323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51539298193656346866247097 38654473645242260149685323)
    ·
      refine ⟨57981710467863390224527985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38654473645242260149685323 57981710467863390224527985)
      ·
        refine ⟨43486282850897542668395989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57981710467863390224527985 43486282850897542668395989)
        ·
          refine ⟨1019209754317911156290531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43486282850897542668395989 1019209754317911156290531)
          ·
            refine ⟨1528814631476866734435797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019209754317911156290531 1528814631476866734435797)
            ·
              refine ⟨35831592925239064088339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1528814631476866734435797 35831592925239064088339)
              ·
                rfl

theorem cell21_1413081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 7].length) (baseStart_1413081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413081 prefixEnd_1413081 := by exact prefixLift 1413081
  have htrace : WordTrace (prefixWord ++ tailWord_1413081) baseStart_1413081 baseEnd_1413081 := by
    simpa [prefixWord, tailWord_1413081, baseEnd_1413081] using wordTrace_append hprefix tailTrace_1413081
  have hstable : (prefixWord ++ tailWord_1413081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413081).length < 2 ^ (prefixWord ++ tailWord_1413081).sum := by decide
  have hdescent : baseEnd_1413081 < baseStart_1413081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413101 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1413101 : Nat := 118140960795 + 1413101 * 2 ^ 59
def prefixEnd_1413101 : Nat := 4983230072969 + 3 ^ 40 * 1413101 * 2
def baseEnd_1413101 : Nat := 322488900599635986461677

theorem tailTrace_1413101 : CollatzResearch.WordTrace tailWord_1413101 prefixEnd_1413101 322488900599635986461677 := by
  unfold tailWord_1413101
  simp only [CollatzResearch.WordTrace]
  refine ⟨51540027653583890281975157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34360018435722593521316771 51540027653583890281975157)
  ·
    refine ⟨4831877592523489713935171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51540027653583890281975157 4831877592523489713935171)
    ·
      refine ⟨7247816388785234570902757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4831877592523489713935171 7247816388785234570902757)
      ·
        refine ⟨1358965572897231482044267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7247816388785234570902757 1358965572897231482044267)
        ·
          refine ⟨2038448359345847223066401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358965572897231482044267 2038448359345847223066401)
          ·
            refine ⟨1528836269509385417299801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2038448359345847223066401 1528836269509385417299801)
            ·
              refine ⟨1146627202132039062974851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528836269509385417299801 1146627202132039062974851)
              ·
                refine ⟨1719940803198058594462277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146627202132039062974851 1719940803198058594462277)
                ·
                  refine ⟨322488900599635986461677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719940803198058594462277 322488900599635986461677)
                  ·
                    rfl

theorem cell21_1413101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1413101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413101 prefixEnd_1413101 := by exact prefixLift 1413101
  have htrace : WordTrace (prefixWord ++ tailWord_1413101) baseStart_1413101 baseEnd_1413101 := by
    simpa [prefixWord, tailWord_1413101, baseEnd_1413101] using wordTrace_append hprefix tailTrace_1413101
  have hstable : (prefixWord ++ tailWord_1413101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413101).length < 2 ^ (prefixWord ++ tailWord_1413101).sum := by decide
  have hdescent : baseEnd_1413101 < baseStart_1413101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413143 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 4]
def baseStart_1413143 : Nat := 118140960795 + 1413143 * 2 ^ 59
def prefixEnd_1413143 : Nat := 4983230072969 + 3 ^ 40 * 1413143 * 2
def baseEnd_1413143 : Nat := 322498485571853246761591

theorem tailTrace_1413143 : CollatzResearch.WordTrace tailWord_1413143 prefixEnd_1413143 322498485571853246761591 := by
  unfold tailWord_1413143
  simp only [CollatzResearch.WordTrace]
  refine ⟨51541559519431731455004083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34361039679621154303336055 51541559519431731455004083)
  ·
    refine ⟨77312339279147597182506125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51541559519431731455004083 77312339279147597182506125)
    ·
      refine ⟨28992127229680348943439797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77312339279147597182506125 28992127229680348943439797)
      ·
        refine ⟨2718011927782532713447481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28992127229680348943439797 2718011927782532713447481)
        ·
          refine ⟨2038508945836899535085611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2718011927782532713447481 2038508945836899535085611)
          ·
            refine ⟨3057763418755349302628417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038508945836899535085611 3057763418755349302628417)
            ·
              refine ⟨2293322564066511976971313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3057763418755349302628417 2293322564066511976971313)
              ·
                refine ⟨1719991923049883982728485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293322564066511976971313 1719991923049883982728485)
                ·
                  refine ⟨322498485571853246761591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719991923049883982728485 322498485571853246761591)
                  ·
                    rfl

theorem cell21_1413143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 4].length) (baseStart_1413143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413143 prefixEnd_1413143 := by exact prefixLift 1413143
  have htrace : WordTrace (prefixWord ++ tailWord_1413143) baseStart_1413143 baseEnd_1413143 := by
    simpa [prefixWord, tailWord_1413143, baseEnd_1413143] using wordTrace_append hprefix tailTrace_1413143
  have hstable : (prefixWord ++ tailWord_1413143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413143).length < 2 ^ (prefixWord ++ tailWord_1413143).sum := by decide
  have hdescent : baseEnd_1413143 < baseStart_1413143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413202 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1413202 : Nat := 118140960795 + 1413202 * 2 ^ 59
def prefixEnd_1413202 : Nat := 4983230072969 + 3 ^ 40 * 1413202 * 2
def baseEnd_1413202 : Nat := 322511950175682255278137

theorem tailTrace_1413202 : CollatzResearch.WordTrace tailWord_1413202 prefixEnd_1413202 322511950175682255278137 := by
  unfold tailWord_1413202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12885927856554496132850465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34362474284145323020934573 12885927856554496132850465)
  ·
    refine ⟨9664445892415872099637849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12885927856554496132850465 9664445892415872099637849)
    ·
      refine ⟨7248334419311904074728387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9664445892415872099637849 7248334419311904074728387)
      ·
        refine ⟨10872501628967856112092581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7248334419311904074728387 10872501628967856112092581)
        ·
          refine ⟨2038594055431473021017359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10872501628967856112092581 2038594055431473021017359)
          ·
            refine ⟨3057891083147209531526039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038594055431473021017359 3057891083147209531526039)
            ·
              refine ⟨4586836624720814297289059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057891083147209531526039 4586836624720814297289059)
              ·
                refine ⟨6880254937081221445933589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586836624720814297289059 6880254937081221445933589)
                ·
                  refine ⟨322511950175682255278137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6880254937081221445933589 322511950175682255278137)
                  ·
                    rfl

theorem cell21_1413202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1413202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413202 prefixEnd_1413202 := by exact prefixLift 1413202
  have htrace : WordTrace (prefixWord ++ tailWord_1413202) baseStart_1413202 baseEnd_1413202 := by
    simpa [prefixWord, tailWord_1413202, baseEnd_1413202] using wordTrace_append hprefix tailTrace_1413202
  have hstable : (prefixWord ++ tailWord_1413202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413202).length < 2 ^ (prefixWord ++ tailWord_1413202).sum := by decide
  have hdescent : baseEnd_1413202 < baseStart_1413202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413264 : List Nat := [2, 1, 1, 1, 1, 1, 9, 2, 3]
def baseStart_1413264 : Nat := 118140960795 + 1413264 * 2 ^ 59
def prefixEnd_1413264 : Nat := 4983230072969 + 3 ^ 40 * 1413264 * 2
def baseEnd_1413264 : Nat := 322526099420383925244677

theorem tailTrace_1413264 : CollatzResearch.WordTrace tailWord_1413264 prefixEnd_1413264 322526099420383925244677 := by
  unfold tailWord_1413264
  simp only [CollatzResearch.WordTrace]
  refine ⟨25772986375996684560079423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34363981834662246080105897 25772986375996684560079423)
  ·
    refine ⟨38659479563995026840119135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25772986375996684560079423 38659479563995026840119135)
    ·
      refine ⟨57989219345992540260178703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38659479563995026840119135 57989219345992540260178703)
      ·
        refine ⟨86983829018988810390268055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57989219345992540260178703 86983829018988810390268055)
        ·
          refine ⟨130475743528483215585402083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86983829018988810390268055 130475743528483215585402083)
          ·
            refine ⟨195713615292724823378103125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130475743528483215585402083 195713615292724823378103125)
            ·
              refine ⟨1146759464605809511981073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 195713615292724823378103125 1146759464605809511981073)
              ·
                refine ⟨860069598454357133985805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146759464605809511981073 860069598454357133985805)
                ·
                  refine ⟨322526099420383925244677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860069598454357133985805 322526099420383925244677)
                  ·
                    rfl

theorem cell21_1413264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_1413264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413264 prefixEnd_1413264 := by exact prefixLift 1413264
  have htrace : WordTrace (prefixWord ++ tailWord_1413264) baseStart_1413264 baseEnd_1413264 := by
    simpa [prefixWord, tailWord_1413264, baseEnd_1413264] using wordTrace_append hprefix tailTrace_1413264
  have hstable : (prefixWord ++ tailWord_1413264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413264).length < 2 ^ (prefixWord ++ tailWord_1413264).sum := by decide
  have hdescent : baseEnd_1413264 < baseStart_1413264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413270 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1413270 : Nat := 118140960795 + 1413270 * 2 ^ 59
def prefixEnd_1413270 : Nat := 4983230072969 + 3 ^ 40 * 1413270 * 2
def baseEnd_1413270 : Nat := 322527468702129248144665

theorem tailTrace_1413270 : CollatzResearch.WordTrace tailWord_1413270 prefixEnd_1413270 322527468702129248144665 := by
  unfold tailWord_1413270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221636974373227009054829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34364127726647754763251509 3221636974373227009054829)
  ·
    refine ⟨1208113865389960128395561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3221636974373227009054829 1208113865389960128395561)
    ·
      refine ⟨906085399042470096296671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1208113865389960128395561 906085399042470096296671)
      ·
        refine ⟨1359128098563705144445007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906085399042470096296671 1359128098563705144445007)
        ·
          refine ⟨2038692147845557716667511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359128098563705144445007 2038692147845557716667511)
          ·
            refine ⟨3058038221768336575001267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038692147845557716667511 3058038221768336575001267)
            ·
              refine ⟨4587057332652504862501901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3058038221768336575001267 4587057332652504862501901)
              ·
                refine ⟨1720146499744689323438213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4587057332652504862501901 1720146499744689323438213)
                ·
                  refine ⟨322527468702129248144665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1720146499744689323438213 322527468702129248144665)
                  ·
                    rfl

theorem cell21_1413270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1413270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413270 prefixEnd_1413270 := by exact prefixLift 1413270
  have htrace : WordTrace (prefixWord ++ tailWord_1413270) baseStart_1413270 baseEnd_1413270 := by
    simpa [prefixWord, tailWord_1413270, baseEnd_1413270] using wordTrace_append hprefix tailTrace_1413270
  have hstable : (prefixWord ++ tailWord_1413270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413270).length < 2 ^ (prefixWord ++ tailWord_1413270).sum := by decide
  have hdescent : baseEnd_1413270 < baseStart_1413270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413323 : List Nat := [1, 1, 1, 1, 3, 2, 5, 4, 3]
def baseStart_1413323 : Nat := 118140960795 + 1413323 * 2 ^ 59
def prefixEnd_1413323 : Nat := 4983230072969 + 3 ^ 40 * 1413323 * 2
def baseEnd_1413323 : Nat := 322539564024212933761223

theorem tailTrace_1413323 : CollatzResearch.WordTrace tailWord_1413323 prefixEnd_1413323 322539564024212933761223 := by
  unfold tailWord_1413323
  simp only [CollatzResearch.WordTrace]
  refine ⟨51548124658779622196556623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34365416439186414797704415 51548124658779622196556623)
  ·
    refine ⟨77322186988169433294834935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51548124658779622196556623 77322186988169433294834935)
    ·
      refine ⟨115983280482254149942252403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77322186988169433294834935 115983280482254149942252403)
      ·
        refine ⟨173974920723381224913378605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115983280482254149942252403 173974920723381224913378605)
        ·
          refine ⟨65240595271267959342516977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173974920723381224913378605 65240595271267959342516977)
          ·
            refine ⟨48930446453450969506887733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65240595271267959342516977 48930446453450969506887733)
            ·
              refine ⟨4587229355011028391270725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48930446453450969506887733 4587229355011028391270725)
              ·
                refine ⟨860105504064567823363261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4587229355011028391270725 860105504064567823363261)
                ·
                  refine ⟨322539564024212933761223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860105504064567823363261 322539564024212933761223)
                  ·
                    rfl

theorem cell21_1413323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 3].length) (baseStart_1413323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413323 prefixEnd_1413323 := by exact prefixLift 1413323
  have htrace : WordTrace (prefixWord ++ tailWord_1413323) baseStart_1413323 baseEnd_1413323 := by
    simpa [prefixWord, tailWord_1413323, baseEnd_1413323] using wordTrace_append hprefix tailTrace_1413323
  have hstable : (prefixWord ++ tailWord_1413323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413323).length < 2 ^ (prefixWord ++ tailWord_1413323).sum := by decide
  have hdescent : baseEnd_1413323 < baseStart_1413323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413337 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 4]
def baseStart_1413337 : Nat := 118140960795 + 1413337 * 2 ^ 59
def prefixEnd_1413337 : Nat := 4983230072969 + 3 ^ 40 * 1413337 * 2
def baseEnd_1413337 : Nat := 322542759014952020527861

theorem tailTrace_1413337 : CollatzResearch.WordTrace tailWord_1413337 prefixEnd_1413337 322542759014952020527861 := by
  unfold tailWord_1413337
  simp only [CollatzResearch.WordTrace]
  refine ⟨51548635280728902587566265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34365756853819268391710843 51548635280728902587566265)
  ·
    refine ⟨38661476460546676940674699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51548635280728902587566265 38661476460546676940674699)
    ·
      refine ⟨57992214690820015411012049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38661476460546676940674699 57992214690820015411012049)
      ·
        refine ⟨43494161018115011558259037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57992214690820015411012049 43494161018115011558259037)
        ·
          refine ⟨16310310381793129334347139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43494161018115011558259037 16310310381793129334347139)
          ·
            refine ⟨24465465572689694001520709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16310310381793129334347139 24465465572689694001520709)
            ·
              refine ⟨4587274794879317625285133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24465465572689694001520709 4587274794879317625285133)
              ·
                refine ⟨1720228048079744109481925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4587274794879317625285133 1720228048079744109481925)
                ·
                  refine ⟨322542759014952020527861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1720228048079744109481925 322542759014952020527861)
                  ·
                    rfl

theorem cell21_1413337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_1413337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413337 prefixEnd_1413337 := by exact prefixLift 1413337
  have htrace : WordTrace (prefixWord ++ tailWord_1413337) baseStart_1413337 baseEnd_1413337 := by
    simpa [prefixWord, tailWord_1413337, baseEnd_1413337] using wordTrace_append hprefix tailTrace_1413337
  have hstable : (prefixWord ++ tailWord_1413337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413337).length < 2 ^ (prefixWord ++ tailWord_1413337).sum := by decide
  have hdescent : baseEnd_1413337 < baseStart_1413337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413357 : List Nat := [1, 5, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1413357 : Nat := 118140960795 + 1413357 * 2 ^ 59
def prefixEnd_1413357 : Nat := 4983230072969 + 3 ^ 40 * 1413357 * 2
def baseEnd_1413357 : Nat := 322547323287436430194487

theorem tailTrace_1413357 : CollatzResearch.WordTrace tailWord_1413357 prefixEnd_1413357 322547323287436430194487 := by
  unfold tailWord_1413357
  simp only [CollatzResearch.WordTrace]
  refine ⟨51549364740656446003294325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34366243160437630668862883 51549364740656446003294325)
  ·
    refine ⟨4832752944436541812808843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51549364740656446003294325 4832752944436541812808843)
    ·
      refine ⟨7249129416654812719213265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832752944436541812808843 7249129416654812719213265)
      ·
        refine ⟨5436847062491109539409949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7249129416654812719213265 5436847062491109539409949)
        ·
          refine ⟨2038817648434166077278731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5436847062491109539409949 2038817648434166077278731)
          ·
            refine ⟨3058226472651249115918097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038817648434166077278731 3058226472651249115918097)
            ·
              refine ⟨2293669854488436836938573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3058226472651249115918097 2293669854488436836938573)
              ·
                refine ⟨860126195433163813851965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2293669854488436836938573 860126195433163813851965)
                ·
                  refine ⟨322547323287436430194487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860126195433163813851965 322547323287436430194487)
                  ·
                    rfl

theorem cell21_1413357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1413357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413357 prefixEnd_1413357 := by exact prefixLift 1413357
  have htrace : WordTrace (prefixWord ++ tailWord_1413357) baseStart_1413357 baseEnd_1413357 := by
    simpa [prefixWord, tailWord_1413357, baseEnd_1413357] using wordTrace_append hprefix tailTrace_1413357
  have hstable : (prefixWord ++ tailWord_1413357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413357).length < 2 ^ (prefixWord ++ tailWord_1413357).sum := by decide
  have hdescent : baseEnd_1413357 < baseStart_1413357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413402 : List Nat := [3, 1, 1, 3, 5, 1, 2, 5]
def baseStart_1413402 : Nat := 118140960795 + 1413402 * 2 ^ 59
def prefixEnd_1413402 : Nat := 4983230072969 + 3 ^ 40 * 1413402 * 2
def baseEnd_1413402 : Nat := 107519197633508783981465

theorem tailTrace_1413402 : CollatzResearch.WordTrace tailWord_1413402 prefixEnd_1413402 107519197633508783981465 := by
  unfold tailWord_1413402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887751506373354672170615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34367337350328945792454973 12887751506373354672170615)
  ·
    refine ⟨19331627259560032008255923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12887751506373354672170615 19331627259560032008255923)
    ·
      refine ⟨28997440889340048012383885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19331627259560032008255923 28997440889340048012383885)
      ·
        refine ⟨10874040333502518004643957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28997440889340048012383885 10874040333502518004643957)
        ·
          refine ⟨1019441281265861062935371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10874040333502518004643957 1019441281265861062935371)
          ·
            refine ⟨1529161921898791594403057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019441281265861062935371 1529161921898791594403057)
            ·
              refine ⟨1146871441424093695802293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529161921898791594403057 1146871441424093695802293)
              ·
                refine ⟨107519197633508783981465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1146871441424093695802293 107519197633508783981465)
                ·
                  rfl

theorem cell21_1413402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_1413402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413402 prefixEnd_1413402 := by exact prefixLift 1413402
  have htrace : WordTrace (prefixWord ++ tailWord_1413402) baseStart_1413402 baseEnd_1413402 := by
    simpa [prefixWord, tailWord_1413402, baseEnd_1413402] using wordTrace_append hprefix tailTrace_1413402
  have hstable : (prefixWord ++ tailWord_1413402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413402).length < 2 ^ (prefixWord ++ tailWord_1413402).sum := by decide
  have hdescent : baseEnd_1413402 < baseStart_1413402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413433 : List Nat := [1, 2, 1, 6, 1, 2, 3, 2, 3]
def baseStart_1413433 : Nat := 118140960795 + 1413433 * 2 ^ 59
def prefixEnd_1413433 : Nat := 4983230072969 + 3 ^ 40 * 1413433 * 2
def baseEnd_1413433 : Nat := 322564667522877186927665

theorem tailTrace_1413433 : CollatzResearch.WordTrace tailWord_1413433 prefixEnd_1413433 322564667522877186927665 := by
  unfold tailWord_1413433
  simp only [CollatzResearch.WordTrace]
  refine ⟨51552136688381110983060953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34368091125587407322040635 51552136688381110983060953)
  ·
    refine ⟨38664102516285833237295715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51552136688381110983060953 38664102516285833237295715)
    ·
      refine ⟨57996153774428749855943573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38664102516285833237295715 57996153774428749855943573)
      ·
        refine ⟨2718569708176347649497355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57996153774428749855943573 2718569708176347649497355)
        ·
          refine ⟨4077854562264521474246033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718569708176347649497355 4077854562264521474246033)
          ·
            refine ⟨3058390921698391105684525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4077854562264521474246033 3058390921698391105684525)
            ·
              refine ⟨1146896595636896664631697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3058390921698391105684525 1146896595636896664631697)
              ·
                refine ⟨860172446727672498473773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146896595636896664631697 860172446727672498473773)
                ·
                  refine ⟨322564667522877186927665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860172446727672498473773 322564667522877186927665)
                  ·
                    rfl

theorem cell21_1413433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_1413433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413433 prefixEnd_1413433 := by exact prefixLift 1413433
  have htrace : WordTrace (prefixWord ++ tailWord_1413433) baseStart_1413433 baseEnd_1413433 := by
    simpa [prefixWord, tailWord_1413433, baseEnd_1413433] using wordTrace_append hprefix tailTrace_1413433
  have hstable : (prefixWord ++ tailWord_1413433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413433).length < 2 ^ (prefixWord ++ tailWord_1413433).sum := by decide
  have hdescent : baseEnd_1413433 < baseStart_1413433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413458 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_1413458 : Nat := 118140960795 + 1413458 * 2 ^ 59
def prefixEnd_1413458 : Nat := 4983230072969 + 3 ^ 40 * 1413458 * 2
def baseEnd_1413458 : Nat := 322570372863482699010947

theorem tailTrace_1413458 : CollatzResearch.WordTrace tailWord_1413458 prefixEnd_1413458 322570372863482699010947 := by
  unfold tailWord_1413458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12888262128322635063180257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34368699008860360168480685 12888262128322635063180257)
  ·
    refine ⟨9666196596241976297385193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12888262128322635063180257 9666196596241976297385193)
    ·
      refine ⟨7249647447181482223038895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9666196596241976297385193 7249647447181482223038895)
      ·
        refine ⟨10874471170772223334558343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7249647447181482223038895 10874471170772223334558343)
        ·
          refine ⟨16311706756158335001837515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10874471170772223334558343 16311706756158335001837515)
          ·
            refine ⟨24467560134237502502756273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16311706756158335001837515 24467560134237502502756273)
            ·
              refine ⟨18350670100678126877067205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24467560134237502502756273 18350670100678126877067205)
              ·
                refine ⟨3440750643877148789450101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18350670100678126877067205 3440750643877148789450101)
                ·
                  refine ⟨322570372863482699010947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3440750643877148789450101 322570372863482699010947)
                  ·
                    rfl

theorem cell21_1413458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_1413458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413458 prefixEnd_1413458 := by exact prefixLift 1413458
  have htrace : WordTrace (prefixWord ++ tailWord_1413458) baseStart_1413458 baseEnd_1413458 := by
    simpa [prefixWord, tailWord_1413458, baseEnd_1413458] using wordTrace_append hprefix tailTrace_1413458
  have hstable : (prefixWord ++ tailWord_1413458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413458).length < 2 ^ (prefixWord ++ tailWord_1413458).sum := by decide
  have hdescent : baseEnd_1413458 < baseStart_1413458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413475 : List Nat := [1, 1, 1, 5, 2, 1, 2, 5, 3]
def baseStart_1413475 : Nat := 118140960795 + 1413475 * 2 ^ 59
def prefixEnd_1413475 : Nat := 4983230072969 + 3 ^ 40 * 1413475 * 2
def baseEnd_1413475 : Nat := 322574252495094447227579

theorem tailTrace_1413475 : CollatzResearch.WordTrace tailWord_1413475 prefixEnd_1413475 322574252495094447227579 := by
  unfold tailWord_1413475
  simp only [CollatzResearch.WordTrace]
  refine ⟨51553668554228952156089879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34369112369485968104059919 51553668554228952156089879)
  ·
    refine ⟨77330502831343428234134819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51553668554228952156089879 77330502831343428234134819)
    ·
      refine ⟨115995754247015142351202229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77330502831343428234134819 115995754247015142351202229)
      ·
        refine ⟨10874601960657669595425209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115995754247015142351202229 10874601960657669595425209)
        ·
          refine ⟨8155951470493252196568907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10874601960657669595425209 8155951470493252196568907)
          ·
            refine ⟨12233927205739878294853361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155951470493252196568907 12233927205739878294853361)
            ·
              refine ⟨9175445404304908721140021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12233927205739878294853361 9175445404304908721140021)
              ·
                refine ⟨860198006653585192606877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9175445404304908721140021 860198006653585192606877)
                ·
                  refine ⟨322574252495094447227579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860198006653585192606877 322574252495094447227579)
                  ·
                    rfl

theorem cell21_1413475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 3].length) (baseStart_1413475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413475 prefixEnd_1413475 := by exact prefixLift 1413475
  have htrace : WordTrace (prefixWord ++ tailWord_1413475) baseStart_1413475 baseEnd_1413475 := by
    simpa [prefixWord, tailWord_1413475, baseEnd_1413475] using wordTrace_append hprefix tailTrace_1413475
  have hstable : (prefixWord ++ tailWord_1413475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413475).length < 2 ^ (prefixWord ++ tailWord_1413475).sum := by decide
  have hdescent : baseEnd_1413475 < baseStart_1413475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413602 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_1413602 : Nat := 118140960795 + 1413602 * 2 ^ 59
def prefixEnd_1413602 : Nat := 4983230072969 + 3 ^ 40 * 1413602 * 2
def baseEnd_1413602 : Nat := 322603235625370448610653

theorem tailTrace_1413602 : CollatzResearch.WordTrace tailWord_1413602 prefixEnd_1413602 322603235625370448610653 := by
  unfold tailWord_1413602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12889575156192213211490765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34372200416512568563975373 12889575156192213211490765)
  ·
    refine ⟨4833590683572079954309037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12889575156192213211490765 4833590683572079954309037)
    ·
      refine ⟨1812596506339529982865889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4833590683572079954309037 1812596506339529982865889)
      ·
        refine ⟨1359447379754647487149417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1812596506339529982865889 1359447379754647487149417)
        ·
          refine ⟨1019585534815985615362063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1359447379754647487149417 1019585534815985615362063)
          ·
            refine ⟨1529378302223978423043095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019585534815985615362063 1529378302223978423043095)
            ·
              refine ⟨2294067453335967634564643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529378302223978423043095 2294067453335967634564643)
              ·
                refine ⟨3441101180003951451846965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294067453335967634564643 3441101180003951451846965)
                ·
                  refine ⟨322603235625370448610653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3441101180003951451846965 322603235625370448610653)
                  ·
                    rfl

theorem cell21_1413602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_1413602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413602 prefixEnd_1413602 := by exact prefixLift 1413602
  have htrace : WordTrace (prefixWord ++ tailWord_1413602) baseStart_1413602 baseEnd_1413602 := by
    simpa [prefixWord, tailWord_1413602, baseEnd_1413602] using wordTrace_append hprefix tailTrace_1413602
  have hstable : (prefixWord ++ tailWord_1413602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413602).length < 2 ^ (prefixWord ++ tailWord_1413602).sum := by decide
  have hdescent : baseEnd_1413602 < baseStart_1413602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413655 : List Nat := [1, 1, 3, 6, 10]
def baseStart_1413655 : Nat := 118140960795 + 1413655 * 2 ^ 59
def prefixEnd_1413655 : Nat := 4983230072969 + 3 ^ 40 * 1413655 * 2
def baseEnd_1413655 : Nat := 3982905320338939928731

theorem tailTrace_1413655 : CollatzResearch.WordTrace tailWord_1413655 prefixEnd_1413655 3982905320338939928731 := by
  unfold tailWord_1413655
  simp only [CollatzResearch.WordTrace]
  refine ⟨51560233693576842897642419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34373489129051228598428279 51560233693576842897642419)
  ·
    refine ⟨77340350540365264346463629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51560233693576842897642419 77340350540365264346463629)
    ·
      refine ⟨29002631452636974129923861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77340350540365264346463629 29002631452636974129923861)
      ·
        refine ⟨1359498349342358162340181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29002631452636974129923861 1359498349342358162340181)
        ·
          refine ⟨3982905320338939928731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1359498349342358162340181 3982905320338939928731)
          ·
            rfl

theorem cell21_1413655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 10].length) (baseStart_1413655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413655 prefixEnd_1413655 := by exact prefixLift 1413655
  have htrace : WordTrace (prefixWord ++ tailWord_1413655) baseStart_1413655 baseEnd_1413655 := by
    simpa [prefixWord, tailWord_1413655, baseEnd_1413655] using wordTrace_append hprefix tailTrace_1413655
  have hstable : (prefixWord ++ tailWord_1413655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413655).length < 2 ^ (prefixWord ++ tailWord_1413655).sum := by decide
  have hdescent : baseEnd_1413655 < baseStart_1413655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413661 : List Nat := [1, 4, 2, 2, 1, 4, 2, 2, 3]
def baseStart_1413661 : Nat := 118140960795 + 1413661 * 2 ^ 59
def prefixEnd_1413661 : Nat := 4983230072969 + 3 ^ 40 * 1413661 * 2
def baseEnd_1413661 : Nat := 322616700229199457127199

theorem tailTrace_1413661 : CollatzResearch.WordTrace tailWord_1413661 prefixEnd_1413661 322616700229199457127199 := by
  unfold tailWord_1413661
  simp only [CollatzResearch.WordTrace]
  refine ⟨51560452531555105922360837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34373635021036737281573891 51560452531555105922360837)
  ·
    refine ⟨9667584849666582360442657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51560452531555105922360837 9667584849666582360442657)
    ·
      refine ⟨7250688637249936770331993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9667584849666582360442657 7250688637249936770331993)
      ·
        refine ⟨5438016477937452577748995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7250688637249936770331993 5438016477937452577748995)
        ·
          refine ⟨8157024716906178866623493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5438016477937452577748995 8157024716906178866623493)
          ·
            refine ⟨1529442134419908537491905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8157024716906178866623493 1529442134419908537491905)
            ·
              refine ⟨1147081600814931403118929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529442134419908537491905 1147081600814931403118929)
              ·
                refine ⟨860311200611198552339197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147081600814931403118929 860311200611198552339197)
                ·
                  refine ⟨322616700229199457127199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860311200611198552339197 322616700229199457127199)
                  ·
                    rfl

theorem cell21_1413661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_1413661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413661 prefixEnd_1413661 := by exact prefixLift 1413661
  have htrace : WordTrace (prefixWord ++ tailWord_1413661) baseStart_1413661 baseEnd_1413661 := by
    simpa [prefixWord, tailWord_1413661, baseEnd_1413661] using wordTrace_append hprefix tailTrace_1413661
  have hstable : (prefixWord ++ tailWord_1413661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413661).length < 2 ^ (prefixWord ++ tailWord_1413661).sum := by decide
  have hdescent : baseEnd_1413661 < baseStart_1413661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413672 : List Nat := [2, 1, 5, 2, 1, 1, 3, 6]
def baseStart_1413672 : Nat := 118140960795 + 1413672 * 2 ^ 59
def prefixEnd_1413672 : Nat := 4983230072969 + 3 ^ 40 * 1413672 * 2
def baseEnd_1413672 : Nat := 107539736859688627481281

theorem tailTrace_1413672 : CollatzResearch.WordTrace tailWord_1413672 prefixEnd_1413672 107539736859688627481281 := by
  unfold tailWord_1413672
  simp only [CollatzResearch.WordTrace]
  refine ⟨25780426867257627400505635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34373902489676836534007513 25780426867257627400505635)
  ·
    refine ⟨38670640300886441100758453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25780426867257627400505635 38670640300886441100758453)
    ·
      refine ⟨3625372528208103853196105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38670640300886441100758453 3625372528208103853196105)
      ·
        refine ⟨2719029396156077889897079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3625372528208103853196105 2719029396156077889897079)
        ·
          refine ⟨4078544094234116834845619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2719029396156077889897079 4078544094234116834845619)
          ·
            refine ⟨6117816141351175252268429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078544094234116834845619 6117816141351175252268429)
            ·
              refine ⟨2294181053006690719600661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6117816141351175252268429 2294181053006690719600661)
              ·
                refine ⟨107539736859688627481281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2294181053006690719600661 107539736859688627481281)
                ·
                  rfl

theorem cell21_1413672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_1413672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413672 prefixEnd_1413672 := by exact prefixLift 1413672
  have htrace : WordTrace (prefixWord ++ tailWord_1413672) baseStart_1413672 baseEnd_1413672 := by
    simpa [prefixWord, tailWord_1413672, baseEnd_1413672] using wordTrace_append hprefix tailTrace_1413672
  have hstable : (prefixWord ++ tailWord_1413672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413672).length < 2 ^ (prefixWord ++ tailWord_1413672).sum := by decide
  have hdescent : baseEnd_1413672 < baseStart_1413672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413703 : List Nat := [1, 1, 4, 1, 4, 1, 1, 5, 3]
def baseStart_1413703 : Nat := 118140960795 + 1413703 * 2 ^ 59
def prefixEnd_1413703 : Nat := 4983230072969 + 3 ^ 40 * 1413703 * 2
def baseEnd_1413703 : Nat := 322626285201416717427113

theorem tailTrace_1413703 : CollatzResearch.WordTrace tailWord_1413703 prefixEnd_1413703 322626285201416717427113 := by
  unfold tailWord_1413703
  simp only [CollatzResearch.WordTrace]
  refine ⟨51561984397402947095389763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34374656264935298063593175 51561984397402947095389763)
  ·
    refine ⟨77342976596104420643084645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51561984397402947095389763 77342976596104420643084645)
    ·
      refine ⟨14501808111769578870578371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77342976596104420643084645 14501808111769578870578371)
      ·
        refine ⟨21752712167654368305867557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14501808111769578870578371 21752712167654368305867557)
        ·
          refine ⟨4078633531435194057350167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21752712167654368305867557 4078633531435194057350167)
          ·
            refine ⟨6117950297152791086025251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078633531435194057350167 6117950297152791086025251)
            ·
              refine ⟨9176925445729186629037877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6117950297152791086025251 9176925445729186629037877)
              ·
                refine ⟨860336760537111246472301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9176925445729186629037877 860336760537111246472301)
                ·
                  refine ⟨322626285201416717427113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860336760537111246472301 322626285201416717427113)
                  ·
                    rfl

theorem cell21_1413703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 3].length) (baseStart_1413703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413703 prefixEnd_1413703 := by exact prefixLift 1413703
  have htrace : WordTrace (prefixWord ++ tailWord_1413703) baseStart_1413703 baseEnd_1413703 := by
    simpa [prefixWord, tailWord_1413703, baseEnd_1413703] using wordTrace_append hprefix tailTrace_1413703
  have hstable : (prefixWord ++ tailWord_1413703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413703).length < 2 ^ (prefixWord ++ tailWord_1413703).sum := by decide
  have hdescent : baseEnd_1413703 < baseStart_1413703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413717 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 4]
def baseStart_1413717 : Nat := 118140960795 + 1413717 * 2 ^ 59
def prefixEnd_1413717 : Nat := 4983230072969 + 3 ^ 40 * 1413717 * 2
def baseEnd_1413717 : Nat := 322629480192155804193751

theorem tailTrace_1413717 : CollatzResearch.WordTrace tailWord_1413717 prefixEnd_1413717 322629480192155804193751 := by
  unfold tailWord_1413717
  simp only [CollatzResearch.WordTrace]
  refine ⟨51562495019352227486399405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34374996679568151657599603 51562495019352227486399405)
  ·
    refine ⟨19335935632257085307399777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51562495019352227486399405 19335935632257085307399777)
    ·
      refine ⟨14501951724192813980549833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19335935632257085307399777 14501951724192813980549833)
      ·
        refine ⟨10876463793144610485412375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14501951724192813980549833 10876463793144610485412375)
        ·
          refine ⟨16314695689716915728118563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10876463793144610485412375 16314695689716915728118563)
          ·
            refine ⟨24472043534575373592177845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16314695689716915728118563 24472043534575373592177845)
            ·
              refine ⟨2294254081366441274266673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24472043534575373592177845 2294254081366441274266673)
              ·
                refine ⟨1720690561024830955700005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2294254081366441274266673 1720690561024830955700005)
                ·
                  refine ⟨322629480192155804193751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1720690561024830955700005 322629480192155804193751)
                  ·
                    rfl

theorem cell21_1413717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_1413717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413717 prefixEnd_1413717 := by exact prefixLift 1413717
  have htrace : WordTrace (prefixWord ++ tailWord_1413717) baseStart_1413717 baseEnd_1413717 := by
    simpa [prefixWord, tailWord_1413717, baseEnd_1413717] using wordTrace_append hprefix tailTrace_1413717
  have hstable : (prefixWord ++ tailWord_1413717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413717).length < 2 ^ (prefixWord ++ tailWord_1413717).sum := by decide
  have hdescent : baseEnd_1413717 < baseStart_1413717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413830 : List Nat := [6, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1413830 : Nat := 118140960795 + 1413830 * 2 ^ 59
def prefixEnd_1413830 : Nat := 4983230072969 + 3 ^ 40 * 1413830 * 2
def baseEnd_1413830 : Nat := 322655268331692718810187

theorem tailTrace_1413830 : CollatzResearch.WordTrace tailWord_1413830 prefixEnd_1413830 322655268331692718810187 := by
  unfold tailWord_1413830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1611456764623213993289467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34377744311961898523508629 1611456764623213993289467)
  ·
    refine ⟨2417185146934820989934201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1611456764623213993289467 2417185146934820989934201)
    ·
      refine ⟨1812888860201115742450651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2417185146934820989934201 1812888860201115742450651)
      ·
        refine ⟨2719333290301673613675977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812888860201115742450651 2719333290301673613675977)
        ·
          refine ⟨2039499967726255210256983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2719333290301673613675977 2039499967726255210256983)
          ·
            refine ⟨3059249951589382815385475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039499967726255210256983 3059249951589382815385475)
            ·
              refine ⟨4588874927384074223078213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059249951589382815385475 4588874927384074223078213)
              ·
                refine ⟨860414048884513916827165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4588874927384074223078213 860414048884513916827165)
                ·
                  refine ⟨322655268331692718810187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860414048884513916827165 322655268331692718810187)
                  ·
                    rfl

theorem cell21_1413830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1413830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413830 prefixEnd_1413830 := by exact prefixLift 1413830
  have htrace : WordTrace (prefixWord ++ tailWord_1413830) baseStart_1413830 baseEnd_1413830 := by
    simpa [prefixWord, tailWord_1413830, baseEnd_1413830] using wordTrace_append hprefix tailTrace_1413830
  have hstable : (prefixWord ++ tailWord_1413830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413830).length < 2 ^ (prefixWord ++ tailWord_1413830).sum := by decide
  have hdescent : baseEnd_1413830 < baseStart_1413830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413886 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1413886 : Nat := 118140960795 + 1413886 * 2 ^ 59
def prefixEnd_1413886 : Nat := 4983230072969 + 3 ^ 40 * 1413886 * 2
def baseEnd_1413886 : Nat := 322668048294649065876739

theorem tailTrace_1413886 : CollatzResearch.WordTrace tailWord_1413886 prefixEnd_1413886 322668048294649065876739 := by
  unfold tailWord_1413886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6446082369467496168662689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34379105970493312899534341 6446082369467496168662689)
  ·
    refine ⟨4834561777100622126497017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6446082369467496168662689 4834561777100622126497017)
    ·
      refine ⟨3625921332825466594872763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4834561777100622126497017 3625921332825466594872763)
      ·
        refine ⟨5438881999238199892309145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3625921332825466594872763 5438881999238199892309145)
        ·
          refine ⟨4079161499428649919231859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5438881999238199892309145 4079161499428649919231859)
          ·
            refine ⟨6118742249142974878847789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079161499428649919231859 6118742249142974878847789)
            ·
              refine ⟨2294528343428615579567921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6118742249142974878847789 2294528343428615579567921)
              ·
                refine ⟨1720896257571461684675941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2294528343428615579567921 1720896257571461684675941)
                ·
                  refine ⟨322668048294649065876739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1720896257571461684675941 322668048294649065876739)
                  ·
                    rfl

theorem cell21_1413886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1413886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413886 prefixEnd_1413886 := by exact prefixLift 1413886
  have htrace : WordTrace (prefixWord ++ tailWord_1413886) baseStart_1413886 baseEnd_1413886 := by
    simpa [prefixWord, tailWord_1413886, baseEnd_1413886] using wordTrace_append hprefix tailTrace_1413886
  have hstable : (prefixWord ++ tailWord_1413886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413886).length < 2 ^ (prefixWord ++ tailWord_1413886).sum := by decide
  have hdescent : baseEnd_1413886 < baseStart_1413886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413897 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 5]
def baseStart_1413897 : Nat := 118140960795 + 1413897 * 2 ^ 59
def prefixEnd_1413897 : Nat := 4983230072969 + 3 ^ 40 * 1413897 * 2
def baseEnd_1413897 : Nat := 322670558644515491193383

theorem tailTrace_1413897 : CollatzResearch.WordTrace tailWord_1413897 prefixEnd_1413897 322670558644515491193383 := by
  unfold tailWord_1413897
  simp only [CollatzResearch.WordTrace]
  refine ⟨51569060158700118227951945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34379373439133412151967963 51569060158700118227951945)
  ·
    refine ⟨38676795119025088670963959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51569060158700118227951945 38676795119025088670963959)
    ·
      refine ⟨58015192678537633006445939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38676795119025088670963959 58015192678537633006445939)
      ·
        refine ⟨87022789017806449509668909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58015192678537633006445939 87022789017806449509668909)
        ·
          refine ⟨32633545881677418566125841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87022789017806449509668909 32633545881677418566125841)
          ·
            refine ⟨24475159411258063924594381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32633545881677418566125841 24475159411258063924594381)
            ·
              refine ⟨9178184779221773971722893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24475159411258063924594381 9178184779221773971722893)
              ·
                refine ⟨3441819292208165239396085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9178184779221773971722893 3441819292208165239396085)
                ·
                  refine ⟨322670558644515491193383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3441819292208165239396085 322670558644515491193383)
                  ·
                    rfl

theorem cell21_1413897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_1413897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413897 prefixEnd_1413897 := by exact prefixLift 1413897
  have htrace : WordTrace (prefixWord ++ tailWord_1413897) baseStart_1413897 baseEnd_1413897 := by
    simpa [prefixWord, tailWord_1413897, baseEnd_1413897] using wordTrace_append hprefix tailTrace_1413897
  have hstable : (prefixWord ++ tailWord_1413897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413897).length < 2 ^ (prefixWord ++ tailWord_1413897).sum := by decide
  have hdescent : baseEnd_1413897 < baseStart_1413897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413928 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_1413928 : Nat := 118140960795 + 1413928 * 2 ^ 59
def prefixEnd_1413928 : Nat := 4983230072969 + 3 ^ 40 * 1413928 * 2
def baseEnd_1413928 : Nat := 322677633266866326176653

theorem tailTrace_1413928 : CollatzResearch.WordTrace tailWord_1413928 prefixEnd_1413928 322677633266866326176653 := by
  unfold tailWord_1413928
  simp only [CollatzResearch.WordTrace]
  refine ⟨25785095410793905261165219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34380127214391873681553625 25785095410793905261165219)
  ·
    refine ⟨38677643116190857891747829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25785095410793905261165219 38677643116190857891747829)
    ·
      refine ⟨3626029042142892927351359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38677643116190857891747829 3626029042142892927351359)
      ·
        refine ⟨5439043563214339391027039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626029042142892927351359 5439043563214339391027039)
        ·
          refine ⟨8158565344821509086540559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5439043563214339391027039 8158565344821509086540559)
          ·
            refine ⟨12237848017232263629810839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8158565344821509086540559 12237848017232263629810839)
            ·
              refine ⟨18356772025848395444716259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12237848017232263629810839 18356772025848395444716259)
              ·
                refine ⟨27535158038772593167074389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18356772025848395444716259 27535158038772593167074389)
                ·
                  refine ⟨322677633266866326176653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27535158038772593167074389 322677633266866326176653)
                  ·
                    rfl

theorem cell21_1413928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_1413928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413928 prefixEnd_1413928 := by exact prefixLift 1413928
  have htrace : WordTrace (prefixWord ++ tailWord_1413928) baseStart_1413928 baseEnd_1413928 := by
    simpa [prefixWord, tailWord_1413928, baseEnd_1413928] using wordTrace_append hprefix tailTrace_1413928
  have hstable : (prefixWord ++ tailWord_1413928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413928).length < 2 ^ (prefixWord ++ tailWord_1413928).sum := by decide
  have hdescent : baseEnd_1413928 < baseStart_1413928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413973 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 7]
def baseStart_1413973 : Nat := 118140960795 + 1413973 * 2 ^ 59
def prefixEnd_1413973 : Nat := 4983230072969 + 3 ^ 40 * 1413973 * 2
def baseEnd_1413973 : Nat := 322687902879956247926561

theorem tailTrace_1413973 : CollatzResearch.WordTrace tailWord_1413973 prefixEnd_1413973 322687902879956247926561 := by
  unfold tailWord_1413973
  simp only [CollatzResearch.WordTrace]
  refine ⟨51571832106424783207718573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34381221404283188805145715 51571832106424783207718573)
  ·
    refine ⟨19339437039909293702894465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51571832106424783207718573 19339437039909293702894465)
    ·
      refine ⟨14504577779931970277170849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19339437039909293702894465 14504577779931970277170849)
      ·
        refine ⟨10878433334948977707878137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14504577779931970277170849 10878433334948977707878137)
        ·
          refine ⟨8158825001211733280908603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10878433334948977707878137 8158825001211733280908603)
          ·
            refine ⟨12238237501817599921362905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8158825001211733280908603 12238237501817599921362905)
            ·
              refine ⟨9178678126363199941022179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12238237501817599921362905 9178678126363199941022179)
              ·
                refine ⟨13768017189544799911533269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9178678126363199941022179 13768017189544799911533269)
                ·
                  refine ⟨322687902879956247926561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13768017189544799911533269 322687902879956247926561)
                  ·
                    rfl

theorem cell21_1413973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_1413973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1413973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1413973 prefixEnd_1413973 := by exact prefixLift 1413973
  have htrace : WordTrace (prefixWord ++ tailWord_1413973) baseStart_1413973 baseEnd_1413973 := by
    simpa [prefixWord, tailWord_1413973, baseEnd_1413973] using wordTrace_append hprefix tailTrace_1413973
  have hstable : (prefixWord ++ tailWord_1413973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413973).length < 2 ^ (prefixWord ++ tailWord_1413973).sum := by decide
  have hdescent : baseEnd_1413973 < baseStart_1413973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414055 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 4]
def baseStart_1414055 : Nat := 118140960795 + 1414055 * 2 ^ 59
def prefixEnd_1414055 : Nat := 4983230072969 + 3 ^ 40 * 1414055 * 2
def baseEnd_1414055 : Nat := 322706616397142327559727

theorem tailTrace_1414055 : CollatzResearch.WordTrace tailWord_1414055 prefixEnd_1414055 322706616397142327559727 := by
  unfold tailWord_1414055
  simp only [CollatzResearch.WordTrace]
  refine ⟨51574822892127711212203619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34383215261418474141469079 51574822892127711212203619)
  ·
    refine ⟨77362234338191566818305429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51574822892127711212203619 77362234338191566818305429)
    ·
      refine ⟨3626354734602729694608067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77362234338191566818305429 3626354734602729694608067)
      ·
        refine ⟨5439532101904094541912101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626354734602729694608067 5439532101904094541912101)
        ·
          refine ⟨1019912269107017726608519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5439532101904094541912101 1019912269107017726608519)
          ·
            refine ⟨1529868403660526589912779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019912269107017726608519 1529868403660526589912779)
            ·
              refine ⟨2294802605490789884869169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529868403660526589912779 2294802605490789884869169)
              ·
                refine ⟨1721101954118092413651877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2294802605490789884869169 1721101954118092413651877)
                ·
                  refine ⟨322706616397142327559727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721101954118092413651877 322706616397142327559727)
                  ·
                    rfl

theorem cell21_1414055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 4].length) (baseStart_1414055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414055 prefixEnd_1414055 := by exact prefixLift 1414055
  have htrace : WordTrace (prefixWord ++ tailWord_1414055) baseStart_1414055 baseEnd_1414055 := by
    simpa [prefixWord, tailWord_1414055, baseEnd_1414055] using wordTrace_append hprefix tailTrace_1414055
  have hstable : (prefixWord ++ tailWord_1414055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414055).length < 2 ^ (prefixWord ++ tailWord_1414055).sum := by decide
  have hdescent : baseEnd_1414055 < baseStart_1414055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414100 : List Nat := [2, 4, 1, 2, 1, 4, 1, 3, 3]
def baseStart_1414100 : Nat := 118140960795 + 1414100 * 2 ^ 59
def prefixEnd_1414100 : Nat := 4983230072969 + 3 ^ 40 * 1414100 * 2
def baseEnd_1414100 : Nat := 322716886010232249309635

theorem tailTrace_1414100 : CollatzResearch.WordTrace tailWord_1414100 prefixEnd_1414100 322716886010232249309635 := by
  unfold tailWord_1414100
  simp only [CollatzResearch.WordTrace]
  refine ⟨25788232088482341948795877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34384309451309789265061169 25788232088482341948795877)
  ·
    refine ⟨4835293516590439115399227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25788232088482341948795877 4835293516590439115399227)
    ·
      refine ⟨7252940274885658673098841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835293516590439115399227 7252940274885658673098841)
      ·
        refine ⟨5439705206164244004824131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7252940274885658673098841 5439705206164244004824131)
        ·
          refine ⟨8159557809246366007236197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5439705206164244004824131 8159557809246366007236197)
          ·
            refine ⟨1529917089233693626356787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8159557809246366007236197 1529917089233693626356787)
            ·
              refine ⟨2294875633850540439535181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529917089233693626356787 2294875633850540439535181)
              ·
                refine ⟨860578362693952664825693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2294875633850540439535181 860578362693952664825693)
                ·
                  refine ⟨322716886010232249309635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860578362693952664825693 322716886010232249309635)
                  ·
                    rfl

theorem cell21_1414100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_1414100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414100 prefixEnd_1414100 := by exact prefixLift 1414100
  have htrace : WordTrace (prefixWord ++ tailWord_1414100) baseStart_1414100 baseEnd_1414100 := by
    simpa [prefixWord, tailWord_1414100, baseEnd_1414100] using wordTrace_append hprefix tailTrace_1414100
  have hstable : (prefixWord ++ tailWord_1414100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414100).length < 2 ^ (prefixWord ++ tailWord_1414100).sum := by decide
  have hdescent : baseEnd_1414100 < baseStart_1414100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414111 : List Nat := [1, 1, 2, 3, 5, 2, 7]
def baseStart_1414111 : Nat := 118140960795 + 1414111 * 2 ^ 59
def prefixEnd_1414111 : Nat := 4983230072969 + 3 ^ 40 * 1414111 * 2
def baseEnd_1414111 : Nat := 35857710706677630514031

theorem tailTrace_1414111 : CollatzResearch.WordTrace tailWord_1414111 prefixEnd_1414111 35857710706677630514031 := by
  unfold tailWord_1414111
  simp only [CollatzResearch.WordTrace]
  refine ⟨51576865379924832776242187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34384576919949888517494791 51576865379924832776242187)
  ·
    refine ⟨77365298069887249164363281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51576865379924832776242187 77365298069887249164363281)
    ·
      refine ⟨58023973552415436873272461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77365298069887249164363281 58023973552415436873272461)
      ·
        refine ⟨21758990082155788827477173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58023973552415436873272461 21758990082155788827477173)
        ·
          refine ⟨2039905320202105202575985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21758990082155788827477173 2039905320202105202575985)
          ·
            refine ⟨1529928990151578901931989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2039905320202105202575985 1529928990151578901931989)
            ·
              refine ⟨35857710706677630514031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1529928990151578901931989 35857710706677630514031)
              ·
                rfl

theorem cell21_1414111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 7].length) (baseStart_1414111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414111 prefixEnd_1414111 := by exact prefixLift 1414111
  have htrace : WordTrace (prefixWord ++ tailWord_1414111) baseStart_1414111 baseEnd_1414111 := by
    simpa [prefixWord, tailWord_1414111, baseEnd_1414111] using wordTrace_append hprefix tailTrace_1414111
  have hstable : (prefixWord ++ tailWord_1414111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414111).length < 2 ^ (prefixWord ++ tailWord_1414111).sum := by decide
  have hdescent : baseEnd_1414111 < baseStart_1414111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414117 : List Nat := [1, 3, 1, 6, 1, 1, 3, 2, 3]
def baseStart_1414117 : Nat := 118140960795 + 1414117 * 2 ^ 59
def prefixEnd_1414117 : Nat := 4983230072969 + 3 ^ 40 * 1414117 * 2
def baseEnd_1414117 : Nat := 322720765641843997526267

theorem tailTrace_1414117 : CollatzResearch.WordTrace tailWord_1414117 prefixEnd_1414117 322720765641843997526267 := by
  unfold tailWord_1414117
  simp only [CollatzResearch.WordTrace]
  refine ⟨51577084217903095800960605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34384722811935397200640403 51577084217903095800960605)
  ·
    refine ⟨19341406581713660925360227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51577084217903095800960605 19341406581713660925360227)
    ·
      refine ⟨29012109872570491388040341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19341406581713660925360227 29012109872570491388040341)
      ·
        refine ⟨1359942650276741783814391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29012109872570491388040341 1359942650276741783814391)
        ·
          refine ⟨2039913975415112675721587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359942650276741783814391 2039913975415112675721587)
          ·
            refine ⟨3059870963122669013582381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039913975415112675721587 3059870963122669013582381)
            ·
              refine ⟨1147451611171000880093393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3059870963122669013582381 1147451611171000880093393)
              ·
                refine ⟨860588708378250660070045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147451611171000880093393 860588708378250660070045)
                ·
                  refine ⟨322720765641843997526267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860588708378250660070045 322720765641843997526267)
                  ·
                    rfl

theorem cell21_1414117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_1414117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414117 prefixEnd_1414117 := by exact prefixLift 1414117
  have htrace : WordTrace (prefixWord ++ tailWord_1414117) baseStart_1414117 baseEnd_1414117 := by
    simpa [prefixWord, tailWord_1414117, baseEnd_1414117] using wordTrace_append hprefix tailTrace_1414117
  have hstable : (prefixWord ++ tailWord_1414117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414117).length < 2 ^ (prefixWord ++ tailWord_1414117).sum := by decide
  have hdescent : baseEnd_1414117 < baseStart_1414117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414176 : List Nat := [2, 1, 1, 7, 1, 1, 1, 4, 3]
def baseStart_1414176 : Nat := 118140960795 + 1414176 * 2 ^ 59
def prefixEnd_1414176 : Nat := 4983230072969 + 3 ^ 40 * 1414176 * 2
def baseEnd_1414176 : Nat := 322734230245673006042813

theorem tailTrace_1414176 : CollatzResearch.WordTrace tailWord_1414176 prefixEnd_1414176 322734230245673006042813 := by
  unfold tailWord_1414176
  simp only [CollatzResearch.WordTrace]
  refine ⟨25789618062344674438679191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34386157416459565918238921 25789618062344674438679191)
  ·
    refine ⟨38684427093517011658018787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25789618062344674438679191 38684427093517011658018787)
    ·
      refine ⟨58026640640275517487028181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38684427093517011658018787 58026640640275517487028181)
      ·
        refine ⟨1359999390006457441102223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 58026640640275517487028181 1359999390006457441102223)
        ·
          refine ⟨2039999085009686161653335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359999390006457441102223 2039999085009686161653335)
          ·
            refine ⟨3059998627514529242480003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039999085009686161653335 3059998627514529242480003)
            ·
              refine ⟨4589997941271793863720005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059998627514529242480003 4589997941271793863720005)
              ·
                refine ⟨860624613988461349447501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4589997941271793863720005 860624613988461349447501)
                ·
                  refine ⟨322734230245673006042813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860624613988461349447501 322734230245673006042813)
                  ·
                    rfl

theorem cell21_1414176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_1414176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414176 prefixEnd_1414176 := by exact prefixLift 1414176
  have htrace : WordTrace (prefixWord ++ tailWord_1414176) baseStart_1414176 baseEnd_1414176 := by
    simpa [prefixWord, tailWord_1414176, baseEnd_1414176] using wordTrace_append hprefix tailTrace_1414176
  have hstable : (prefixWord ++ tailWord_1414176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414176).length < 2 ^ (prefixWord ++ tailWord_1414176).sum := by decide
  have hdescent : baseEnd_1414176 < baseStart_1414176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414201 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 7]
def baseStart_1414201 : Nat := 118140960795 + 1414201 * 2 ^ 59
def prefixEnd_1414201 : Nat := 4983230072969 + 3 ^ 40 * 1414201 * 2
def baseEnd_1414201 : Nat := 322739935586278518126095

theorem tailTrace_1414201 : CollatzResearch.WordTrace tailWord_1414201 prefixEnd_1414201 322739935586278518126095 := by
  unfold tailWord_1414201
  simp only [CollatzResearch.WordTrace]
  refine ⟨51580147949598778147018457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34386765299732518764678971 51580147949598778147018457)
  ·
    refine ⟨38685110962199083610263843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51580147949598778147018457 38685110962199083610263843)
    ·
      refine ⟨58027666443298625415395765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38685110962199083610263843 58027666443298625415395765)
      ·
        refine ⟨5440093729059246132693353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58027666443298625415395765 5440093729059246132693353)
        ·
          refine ⟨4080070296794434599520015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5440093729059246132693353 4080070296794434599520015)
          ·
            refine ⟨6120105445191651899280023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080070296794434599520015 6120105445191651899280023)
            ·
              refine ⟨9180158167787477848920035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120105445191651899280023 9180158167787477848920035)
              ·
                refine ⟨13770237251681216773380053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9180158167787477848920035 13770237251681216773380053)
                ·
                  refine ⟨322739935586278518126095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13770237251681216773380053 322739935586278518126095)
                  ·
                    rfl

theorem cell21_1414201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_1414201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414201 prefixEnd_1414201 := by exact prefixLift 1414201
  have htrace : WordTrace (prefixWord ++ tailWord_1414201) baseStart_1414201 baseEnd_1414201 := by
    simpa [prefixWord, tailWord_1414201, baseEnd_1414201] using wordTrace_append hprefix tailTrace_1414201
  have hstable : (prefixWord ++ tailWord_1414201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414201).length < 2 ^ (prefixWord ++ tailWord_1414201).sum := by decide
  have hdescent : baseEnd_1414201 < baseStart_1414201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414218 : List Nat := [3, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_1414218 : Nat := 118140960795 + 1414218 * 2 ^ 59
def prefixEnd_1414218 : Nat := 4983230072969 + 3 ^ 40 * 1414218 * 2
def baseEnd_1414218 : Nat := 322743815217890266342727

theorem tailTrace_1414218 : CollatzResearch.WordTrace tailWord_1414218 prefixEnd_1414218 322743815217890266342727 := by
  unfold tailWord_1414218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12895191997634297512596827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34387178660358126700258205 12895191997634297512596827)
  ·
    refine ⟨19342787996451446268895241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12895191997634297512596827 19342787996451446268895241)
    ·
      refine ⟨14507090997338584701671431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19342787996451446268895241 14507090997338584701671431)
      ·
        refine ⟨21760636496007877052507147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14507090997338584701671431 21760636496007877052507147)
        ·
          refine ⟨32640954744011815578760721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21760636496007877052507147 32640954744011815578760721)
          ·
            refine ⟨24480716058008861684070541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32640954744011815578760721 24480716058008861684070541)
            ·
              refine ⟨9180268521753323131526453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24480716058008861684070541 9180268521753323131526453)
              ·
                refine ⟨860650173914374043580605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9180268521753323131526453 860650173914374043580605)
                ·
                  refine ⟨322743815217890266342727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860650173914374043580605 322743815217890266342727)
                  ·
                    rfl

theorem cell21_1414218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_1414218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414218 prefixEnd_1414218 := by exact prefixLift 1414218
  have htrace : WordTrace (prefixWord ++ tailWord_1414218) baseStart_1414218 baseEnd_1414218 := by
    simpa [prefixWord, tailWord_1414218, baseEnd_1414218] using wordTrace_append hprefix tailTrace_1414218
  have hstable : (prefixWord ++ tailWord_1414218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414218).length < 2 ^ (prefixWord ++ tailWord_1414218).sum := by decide
  have hdescent : baseEnd_1414218 < baseStart_1414218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414249 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 4]
def baseStart_1414249 : Nat := 118140960795 + 1414249 * 2 ^ 59
def prefixEnd_1414249 : Nat := 4983230072969 + 3 ^ 40 * 1414249 * 2
def baseEnd_1414249 : Nat := 322750889840241101325997

theorem tailTrace_1414249 : CollatzResearch.WordTrace tailWord_1414249 prefixEnd_1414249 322750889840241101325997 := by
  unfold tailWord_1414249
  simp only [CollatzResearch.WordTrace]
  refine ⟨51581898653424882344765801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34387932435616588229843867 51581898653424882344765801)
  ·
    refine ⟨38686423990068661758574351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51581898653424882344765801 38686423990068661758574351)
    ·
      refine ⟨58029635985102992637861527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38686423990068661758574351 58029635985102992637861527)
      ·
        refine ⟨87044453977654488956792291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58029635985102992637861527 87044453977654488956792291)
        ·
          refine ⟨130566680966481733435188437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87044453977654488956792291 130566680966481733435188437)
          ·
            refine ⟨3060156585151915627387229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 130566680966481733435188437 3060156585151915627387229)
            ·
              refine ⟨1147558719431968360270211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3060156585151915627387229 1147558719431968360270211)
              ·
                refine ⟨1721338079147952540405317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147558719431968360270211 1721338079147952540405317)
                ·
                  refine ⟨322750889840241101325997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721338079147952540405317 322750889840241101325997)
                  ·
                    rfl

theorem cell21_1414249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_1414249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414249 prefixEnd_1414249 := by exact prefixLift 1414249
  have htrace : WordTrace (prefixWord ++ tailWord_1414249) baseStart_1414249 baseEnd_1414249 := by
    simpa [prefixWord, tailWord_1414249, baseEnd_1414249] using wordTrace_append hprefix tailTrace_1414249
  have hstable : (prefixWord ++ tailWord_1414249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414249).length < 2 ^ (prefixWord ++ tailWord_1414249).sum := by decide
  have hdescent : baseEnd_1414249 < baseStart_1414249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414280 : List Nat := [2, 1, 3, 4, 3, 1, 7]
def baseStart_1414280 : Nat := 118140960795 + 1414280 * 2 ^ 59
def prefixEnd_1414280 : Nat := 4983230072969 + 3 ^ 40 * 1414280 * 2
def baseEnd_1414280 : Nat := 35861996051399104034363

theorem tailTrace_1414280 : CollatzResearch.WordTrace tailWord_1414280 prefixEnd_1414280 35861996051399104034363 := by
  unfold tailWord_1414280
  simp only [CollatzResearch.WordTrace]
  refine ⟨25791514658156287319572147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34388686210875049759429529 25791514658156287319572147)
  ·
    refine ⟨38687271987234430979358221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25791514658156287319572147 38687271987234430979358221)
    ·
      refine ⟨14507726995212911617259333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38687271987234430979358221 14507726995212911617259333)
      ·
        refine ⟨2720198811602420928236125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14507726995212911617259333 2720198811602420928236125)
        ·
          refine ⟨1020074554350907848088547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2720198811602420928236125 1020074554350907848088547)
          ·
            refine ⟨1530111831526361772132821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020074554350907848088547 1530111831526361772132821)
            ·
              refine ⟨35861996051399104034363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1530111831526361772132821 35861996051399104034363)
              ·
                rfl

theorem cell21_1414280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 7].length) (baseStart_1414280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414280 prefixEnd_1414280 := by exact prefixLift 1414280
  have htrace : WordTrace (prefixWord ++ tailWord_1414280) baseStart_1414280 baseEnd_1414280 := by
    simpa [prefixWord, tailWord_1414280, baseEnd_1414280] using wordTrace_append hprefix tailTrace_1414280
  have hstable : (prefixWord ++ tailWord_1414280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414280).length < 2 ^ (prefixWord ++ tailWord_1414280).sum := by decide
  have hdescent : baseEnd_1414280 < baseStart_1414280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414291 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 6]
def baseStart_1414291 : Nat := 118140960795 + 1414291 * 2 ^ 59
def prefixEnd_1414291 : Nat := 4983230072969 + 3 ^ 40 * 1414291 * 2
def baseEnd_1414291 : Nat := 322760474812458361625911

theorem tailTrace_1414291 : CollatzResearch.WordTrace tailWord_1414291 prefixEnd_1414291 322760474812458361625911 := by
  unfold tailWord_1414291
  simp only [CollatzResearch.WordTrace]
  refine ⟨51583430519272723517794727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34388953679515149011863151 51583430519272723517794727)
  ·
    refine ⟨77375145778909085276692091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51583430519272723517794727 77375145778909085276692091)
    ·
      refine ⟨116062718668363627915038137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77375145778909085276692091 116062718668363627915038137)
      ·
        refine ⟨87047039001272720936278603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116062718668363627915038137 87047039001272720936278603)
        ·
          refine ⟨130570558501909081404417905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87047039001272720936278603 130570558501909081404417905)
          ·
            refine ⟨97927918876431811053313429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130570558501909081404417905 97927918876431811053313429)
            ·
              refine ⟨4590371197332741143124067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97927918876431811053313429 4590371197332741143124067)
              ·
                refine ⟨6885556795999111714686101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590371197332741143124067 6885556795999111714686101)
                ·
                  refine ⟨322760474812458361625911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6885556795999111714686101 322760474812458361625911)
                  ·
                    rfl

theorem cell21_1414291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_1414291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414291 prefixEnd_1414291 := by exact prefixLift 1414291
  have htrace : WordTrace (prefixWord ++ tailWord_1414291) baseStart_1414291 baseEnd_1414291 := by
    simpa [prefixWord, tailWord_1414291, baseEnd_1414291] using wordTrace_append hprefix tailTrace_1414291
  have hstable : (prefixWord ++ tailWord_1414291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414291).length < 2 ^ (prefixWord ++ tailWord_1414291).sum := by decide
  have hdescent : baseEnd_1414291 < baseStart_1414291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414322 : List Nat := [3, 2, 1, 1, 1, 4, 2, 7]
def baseStart_1414322 : Nat := 118140960795 + 1414322 * 2 ^ 59
def prefixEnd_1414322 : Nat := 4983230072969 + 3 ^ 40 * 1414322 * 2
def baseEnd_1414322 : Nat := 107589183144936398869727

theorem tailTrace_1414322 : CollatzResearch.WordTrace tailWord_1414322 prefixEnd_1414322 107589183144936398869727 := by
  unfold tailWord_1414322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12896140295540103953043305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34389707454773610541448813 12896140295540103953043305)
  ·
    refine ⟨9672105221655077964782479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12896140295540103953043305 9672105221655077964782479)
    ·
      refine ⟨14508157832482616947173719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9672105221655077964782479 14508157832482616947173719)
      ·
        refine ⟨21762236748723925420760579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14508157832482616947173719 21762236748723925420760579)
        ·
          refine ⟨32643355123085888131140869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21762236748723925420760579 32643355123085888131140869)
          ·
            refine ⟨6120629085578604024588913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32643355123085888131140869 6120629085578604024588913)
            ·
              refine ⟨4590471814183953018441685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6120629085578604024588913 4590471814183953018441685)
              ·
                refine ⟨107589183144936398869727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4590471814183953018441685 107589183144936398869727)
                ·
                  rfl

theorem cell21_1414322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_1414322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414322 prefixEnd_1414322 := by exact prefixLift 1414322
  have htrace : WordTrace (prefixWord ++ tailWord_1414322) baseStart_1414322 baseEnd_1414322 := by
    simpa [prefixWord, tailWord_1414322, baseEnd_1414322] using wordTrace_append hprefix tailTrace_1414322
  have hstable : (prefixWord ++ tailWord_1414322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414322).length < 2 ^ (prefixWord ++ tailWord_1414322).sum := by decide
  have hdescent : baseEnd_1414322 < baseStart_1414322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414401 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 4]
def baseStart_1414401 : Nat := 118140960795 + 1414401 * 2 ^ 59
def prefixEnd_1414401 : Nat := 4983230072969 + 3 ^ 40 * 1414401 * 2
def baseEnd_1414401 : Nat := 322785578311122614792353

theorem tailTrace_1414401 : CollatzResearch.WordTrace tailWord_1414401 prefixEnd_1414401 322785578311122614792353 := by
  unfold tailWord_1414401
  simp only [CollatzResearch.WordTrace]
  refine ⟨51587442548874212304299057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34391628365916141536199371 51587442548874212304299057)
  ·
    refine ⟨38690581911655659228224293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51587442548874212304299057 38690581911655659228224293)
    ·
      refine ⟨7254484108435436105292055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38690581911655659228224293 7254484108435436105292055)
      ·
        refine ⟨10881726162653154157938083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7254484108435436105292055 10881726162653154157938083)
        ·
          refine ⟨16322589243979731236907125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10881726162653154157938083 16322589243979731236907125)
          ·
            refine ⟨1530242741623099803460043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16322589243979731236907125 1530242741623099803460043)
            ·
              refine ⟨2295364112434649705190065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530242741623099803460043 2295364112434649705190065)
              ·
                refine ⟨1721523084325987278892549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2295364112434649705190065 1721523084325987278892549)
                ·
                  refine ⟨322785578311122614792353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721523084325987278892549 322785578311122614792353)
                  ·
                    rfl

theorem cell21_1414401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_1414401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414401 prefixEnd_1414401 := by exact prefixLift 1414401
  have htrace : WordTrace (prefixWord ++ tailWord_1414401) baseStart_1414401 baseEnd_1414401 := by
    simpa [prefixWord, tailWord_1414401, baseEnd_1414401] using wordTrace_append hprefix tailTrace_1414401
  have hstable : (prefixWord ++ tailWord_1414401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414401).length < 2 ^ (prefixWord ++ tailWord_1414401).sum := by decide
  have hdescent : baseEnd_1414401 < baseStart_1414401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414432 : List Nat := [2, 1, 1, 5, 3, 2, 2, 5]
def baseStart_1414432 : Nat := 118140960795 + 1414432 * 2 ^ 59
def prefixEnd_1414432 : Nat := 4983230072969 + 3 ^ 40 * 1414432 * 2
def baseEnd_1414432 : Nat := 107597550977824483258541

theorem tailTrace_1414432 : CollatzResearch.WordTrace tailWord_1414432 prefixEnd_1414432 107597550977824483258541 := by
  unfold tailWord_1414432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25794286605880952299338775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34392382141174603065785033 25794286605880952299338775)
  ·
    refine ⟨38691429908821428449008163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25794286605880952299338775 38691429908821428449008163)
    ·
      refine ⟨58037144863232142673512245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38691429908821428449008163 58037144863232142673512245)
      ·
        refine ⟨5440982330928013375641773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58037144863232142673512245 5440982330928013375641773)
        ·
          refine ⟨2040368374098005015865665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5440982330928013375641773 2040368374098005015865665)
          ·
            refine ⟨1530276280573503761899249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2040368374098005015865665 1530276280573503761899249)
            ·
              refine ⟨1147707210430127821424437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530276280573503761899249 1147707210430127821424437)
              ·
                refine ⟨107597550977824483258541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1147707210430127821424437 107597550977824483258541)
                ·
                  rfl

theorem cell21_1414432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_1414432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414432 prefixEnd_1414432 := by exact prefixLift 1414432
  have htrace : WordTrace (prefixWord ++ tailWord_1414432) baseStart_1414432 baseEnd_1414432 := by
    simpa [prefixWord, tailWord_1414432, baseEnd_1414432] using wordTrace_append hprefix tailTrace_1414432
  have hstable : (prefixWord ++ tailWord_1414432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414432).length < 2 ^ (prefixWord ++ tailWord_1414432).sum := by decide
  have hdescent : baseEnd_1414432 < baseStart_1414432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414463 : List Nat := [1, 1, 2, 2, 4, 3, 3, 2, 3]
def baseStart_1414463 : Nat := 118140960795 + 1414463 * 2 ^ 59
def prefixEnd_1414463 : Nat := 4983230072969 + 3 ^ 40 * 1414463 * 2
def baseEnd_1414463 : Nat := 322799727555824284758893

theorem tailTrace_1414463 : CollatzResearch.WordTrace tailWord_1414463 prefixEnd_1414463 322799727555824284758893 := by
  unfold tailWord_1414463
  simp only [CollatzResearch.WordTrace]
  refine ⟨51589703874649596893056043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34393135916433064595370695 51589703874649596893056043)
  ·
    refine ⟨77384555811974395339584065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51589703874649596893056043 77384555811974395339584065)
    ·
      refine ⟨58038416858980796504688049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77384555811974395339584065 58038416858980796504688049)
      ·
        refine ⟨43528812644235597378516037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58038416858980796504688049 43528812644235597378516037)
        ·
          refine ⟨8161652370794174508471757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43528812644235597378516037 8161652370794174508471757)
          ·
            refine ⟨3060619639047815440676909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8161652370794174508471757 3060619639047815440676909)
            ·
              refine ⟨1147732364642930790253841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3060619639047815440676909 1147732364642930790253841)
              ·
                refine ⟨860799273482198092690381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147732364642930790253841 860799273482198092690381)
                ·
                  refine ⟨322799727555824284758893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860799273482198092690381 322799727555824284758893)
                  ·
                    rfl

theorem cell21_1414463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 3].length) (baseStart_1414463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414463 prefixEnd_1414463 := by exact prefixLift 1414463
  have htrace : WordTrace (prefixWord ++ tailWord_1414463) baseStart_1414463 baseEnd_1414463 := by
    simpa [prefixWord, tailWord_1414463, baseEnd_1414463] using wordTrace_append hprefix tailTrace_1414463
  have hstable : (prefixWord ++ tailWord_1414463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414463).length < 2 ^ (prefixWord ++ tailWord_1414463).sum := by decide
  have hdescent : baseEnd_1414463 < baseStart_1414463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414488 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_1414488 : Nat := 118140960795 + 1414488 * 2 ^ 59
def prefixEnd_1414488 : Nat := 4983230072969 + 3 ^ 40 * 1414488 * 2
def baseEnd_1414488 : Nat := 322805432896429796842175

theorem tailTrace_1414488 : CollatzResearch.WordTrace tailWord_1414488 prefixEnd_1414488 322805432896429796842175 := by
  unfold tailWord_1414488
  simp only [CollatzResearch.WordTrace]
  refine ⟨25795307849779513081358059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34393743799706017441810745 25795307849779513081358059)
  ·
    refine ⟨38692961774669269622037089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25795307849779513081358059 38692961774669269622037089)
    ·
      refine ⟨29019721331001952216527817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38692961774669269622037089 29019721331001952216527817)
      ·
        refine ⟨21764790998251464162395863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29019721331001952216527817 21764790998251464162395863)
        ·
          refine ⟨32647186497377196243593795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21764790998251464162395863 32647186497377196243593795)
          ·
            refine ⟨48970779746065794365390693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32647186497377196243593795 48970779746065794365390693)
            ·
              refine ⟨9182021202387336443510755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48970779746065794365390693 9182021202387336443510755)
              ·
                refine ⟨13773031803581004665266133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9182021202387336443510755 13773031803581004665266133)
                ·
                  refine ⟨322805432896429796842175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13773031803581004665266133 322805432896429796842175)
                  ·
                    rfl

theorem cell21_1414488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_1414488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414488 prefixEnd_1414488 := by exact prefixLift 1414488
  have htrace : WordTrace (prefixWord ++ tailWord_1414488) baseStart_1414488 baseEnd_1414488 := by
    simpa [prefixWord, tailWord_1414488, baseEnd_1414488] using wordTrace_append hprefix tailTrace_1414488
  have hstable : (prefixWord ++ tailWord_1414488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414488).length < 2 ^ (prefixWord ++ tailWord_1414488).sum := by decide
  have hdescent : baseEnd_1414488 < baseStart_1414488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414536 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_1414536 : Nat := 118140960795 + 1414536 * 2 ^ 59
def prefixEnd_1414536 : Nat := 4983230072969 + 3 ^ 40 * 1414536 * 2
def baseEnd_1414536 : Nat := 322816387150392380042077

theorem tailTrace_1414536 : CollatzResearch.WordTrace tailWord_1414536 prefixEnd_1414536 322816387150392380042077 := by
  unfold tailWord_1414536
  simp only [CollatzResearch.WordTrace]
  refine ⟨25796183201692565180231731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34394910935590086906975641 25796183201692565180231731)
  ·
    refine ⟨38694274802538847770347597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25796183201692565180231731 38694274802538847770347597)
    ·
      refine ⟨14510353050952067913880349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38694274802538847770347597 14510353050952067913880349)
      ·
        refine ⟨5441382394107025467705131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14510353050952067913880349 5441382394107025467705131)
        ·
          refine ⟨8162073591160538201557697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441382394107025467705131 8162073591160538201557697)
          ·
            refine ⟨6121555193370403651168273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8162073591160538201557697 6121555193370403651168273)
            ·
              refine ⟨4591166395027802738376205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6121555193370403651168273 4591166395027802738376205)
              ·
                refine ⟨1721687398135426026891077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4591166395027802738376205 1721687398135426026891077)
                ·
                  refine ⟨322816387150392380042077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721687398135426026891077 322816387150392380042077)
                  ·
                    rfl

theorem cell21_1414536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_1414536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414536 prefixEnd_1414536 := by exact prefixLift 1414536
  have htrace : WordTrace (prefixWord ++ tailWord_1414536) baseStart_1414536 baseEnd_1414536 := by
    simpa [prefixWord, tailWord_1414536, baseEnd_1414536] using wordTrace_append hprefix tailTrace_1414536
  have hstable : (prefixWord ++ tailWord_1414536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414536).length < 2 ^ (prefixWord ++ tailWord_1414536).sum := by decide
  have hdescent : baseEnd_1414536 < baseStart_1414536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414556 : List Nat := [2, 2, 3, 4, 1, 1, 2, 3, 3]
def baseStart_1414556 : Nat := 118140960795 + 1414556 * 2 ^ 59
def prefixEnd_1414556 : Nat := 4983230072969 + 3 ^ 40 * 1414556 * 2
def baseEnd_1414556 : Nat := 322820951422876789708703

theorem tailTrace_1414556 : CollatzResearch.WordTrace tailWord_1414556 prefixEnd_1414556 322820951422876789708703 := by
  unfold tailWord_1414556
  simp only [CollatzResearch.WordTrace]
  refine ⟨25796547931656336888095761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34395397242208449184127681 25796547931656336888095761)
  ·
    refine ⟨19347410948742252666071821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25796547931656336888095761 19347410948742252666071821)
    ·
      refine ⟨7255279105778344749776933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19347410948742252666071821 7255279105778344749776933)
      ·
        refine ⟨1360364832333439640583175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7255279105778344749776933 1360364832333439640583175)
        ·
          refine ⟨2040547248500159460874763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360364832333439640583175 2040547248500159460874763)
          ·
            refine ⟨3060820872750239191312145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040547248500159460874763 3060820872750239191312145)
            ·
              refine ⟨2295615654562679393484109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3060820872750239191312145 2295615654562679393484109)
              ·
                refine ⟨860855870461004772556541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2295615654562679393484109 860855870461004772556541)
                ·
                  refine ⟨322820951422876789708703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860855870461004772556541 322820951422876789708703)
                  ·
                    rfl

theorem cell21_1414556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_1414556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414556 prefixEnd_1414556 := by exact prefixLift 1414556
  have htrace : WordTrace (prefixWord ++ tailWord_1414556) baseStart_1414556 baseEnd_1414556 := by
    simpa [prefixWord, tailWord_1414556, baseEnd_1414556] using wordTrace_append hprefix tailTrace_1414556
  have hstable : (prefixWord ++ tailWord_1414556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414556).length < 2 ^ (prefixWord ++ tailWord_1414556).sum := by decide
  have hdescent : baseEnd_1414556 < baseStart_1414556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414564 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_1414564 : Nat := 118140960795 + 1414564 * 2 ^ 59
def prefixEnd_1414564 : Nat := 4983230072969 + 3 ^ 40 * 1414564 * 2
def baseEnd_1414564 : Nat := 322822777131870553575353

theorem tailTrace_1414564 : CollatzResearch.WordTrace tailWord_1414564 prefixEnd_1414564 322822777131870553575353 := by
  unfold tailWord_1414564
  simp only [CollatzResearch.WordTrace]
  refine ⟨25796693823641845571241373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34395591764855794094988497 25796693823641845571241373)
  ·
    refine ⟨9673760183865692089215515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25796693823641845571241373 9673760183865692089215515)
    ·
      refine ⟨14510640275798538133823273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9673760183865692089215515 14510640275798538133823273)
      ·
        refine ⟨10882980206848903600367455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14510640275798538133823273 10882980206848903600367455)
        ·
          refine ⟨16324470310273355400551183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10882980206848903600367455 16324470310273355400551183)
          ·
            refine ⟨24486705465410033100826775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16324470310273355400551183 24486705465410033100826775)
            ·
              refine ⟨36730058198115049651240163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24486705465410033100826775 36730058198115049651240163)
              ·
                refine ⟨55095087297172574476860245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36730058198115049651240163 55095087297172574476860245)
                ·
                  refine ⟨322822777131870553575353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55095087297172574476860245 322822777131870553575353)
                  ·
                    rfl

theorem cell21_1414564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_1414564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414564 prefixEnd_1414564 := by exact prefixLift 1414564
  have htrace : WordTrace (prefixWord ++ tailWord_1414564) baseStart_1414564 baseEnd_1414564 := by
    simpa [prefixWord, tailWord_1414564, baseEnd_1414564] using wordTrace_append hprefix tailTrace_1414564
  have hstable : (prefixWord ++ tailWord_1414564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414564).length < 2 ^ (prefixWord ++ tailWord_1414564).sum := by decide
  have hdescent : baseEnd_1414564 < baseStart_1414564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414581 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 5]
def baseStart_1414581 : Nat := 118140960795 + 1414581 * 2 ^ 59
def prefixEnd_1414581 : Nat := 4983230072969 + 3 ^ 40 * 1414581 * 2
def baseEnd_1414581 : Nat := 322826656763482301791985

theorem tailTrace_1414581 : CollatzResearch.WordTrace tailWord_1414581 prefixEnd_1414581 322826656763482301791985 := by
  unfold tailWord_1414581
  simp only [CollatzResearch.WordTrace]
  refine ⟨51594007688222103045851597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34396005125481402030567731 51594007688222103045851597)
  ·
    refine ⟨19347752883083288642194349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51594007688222103045851597 19347752883083288642194349)
    ·
      refine ⟨7255407331156233240822881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19347752883083288642194349 7255407331156233240822881)
      ·
        refine ⟨5441555498367174930617161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7255407331156233240822881 5441555498367174930617161)
        ·
          refine ⟨4081166623775381197962871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5441555498367174930617161 4081166623775381197962871)
          ·
            refine ⟨6121749935663071796944307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4081166623775381197962871 6121749935663071796944307)
            ·
              refine ⟨9182624903494607695416461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6121749935663071796944307 9182624903494607695416461)
              ·
                refine ⟨3443484338810477885781173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9182624903494607695416461 3443484338810477885781173)
                ·
                  refine ⟨322826656763482301791985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3443484338810477885781173 322826656763482301791985)
                  ·
                    rfl

theorem cell21_1414581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_1414581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414581 prefixEnd_1414581 := by exact prefixLift 1414581
  have htrace : WordTrace (prefixWord ++ tailWord_1414581) baseStart_1414581 baseEnd_1414581 := by
    simpa [prefixWord, tailWord_1414581, baseEnd_1414581] using wordTrace_append hprefix tailTrace_1414581
  have hstable : (prefixWord ++ tailWord_1414581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414581).length < 2 ^ (prefixWord ++ tailWord_1414581).sum := by decide
  have hdescent : baseEnd_1414581 < baseStart_1414581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414595 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 4]
def baseStart_1414595 : Nat := 118140960795 + 1414595 * 2 ^ 59
def prefixEnd_1414595 : Nat := 4983230072969 + 3 ^ 40 * 1414595 * 2
def baseEnd_1414595 : Nat := 322829851754221388558623

theorem tailTrace_1414595 : CollatzResearch.WordTrace tailWord_1414595 prefixEnd_1414595 322829851754221388558623 := by
  unfold tailWord_1414595
  simp only [CollatzResearch.WordTrace]
  refine ⟨51594518310171383436861239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34396345540114255624574159 51594518310171383436861239)
  ·
    refine ⟨77391777465257075155291859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51594518310171383436861239 77391777465257075155291859)
    ·
      refine ⟨116087666197885612732937789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77391777465257075155291859 116087666197885612732937789)
      ·
        refine ⟨43532874824207104774851671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116087666197885612732937789 43532874824207104774851671)
        ·
          refine ⟨65299312236310657162277507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43532874824207104774851671 65299312236310657162277507)
          ·
            refine ⟨97948968354465985743416261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65299312236310657162277507 97948968354465985743416261)
            ·
              refine ⟨18365431566462372326890549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97948968354465985743416261 18365431566462372326890549)
              ·
                refine ⟨1721759209355847405645989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18365431566462372326890549 1721759209355847405645989)
                ·
                  refine ⟨322829851754221388558623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721759209355847405645989 322829851754221388558623)
                  ·
                    rfl

theorem cell21_1414595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 4].length) (baseStart_1414595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414595 prefixEnd_1414595 := by exact prefixLift 1414595
  have htrace : WordTrace (prefixWord ++ tailWord_1414595) baseStart_1414595 baseEnd_1414595 := by
    simpa [prefixWord, tailWord_1414595, baseEnd_1414595] using wordTrace_append hprefix tailTrace_1414595
  have hstable : (prefixWord ++ tailWord_1414595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414595).length < 2 ^ (prefixWord ++ tailWord_1414595).sum := by decide
  have hdescent : baseEnd_1414595 < baseStart_1414595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414646 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1414646 : Nat := 118140960795 + 1414646 * 2 ^ 59
def prefixEnd_1414646 : Nat := 4983230072969 + 3 ^ 40 * 1414646 * 2
def baseEnd_1414646 : Nat := 322841490649056633208519

theorem tailTrace_1414646 : CollatzResearch.WordTrace tailWord_1414646 prefixEnd_1414646 322841490649056633208519 := by
  unfold tailWord_1414646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3224773652061663696685487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34397585621991079431311861 3224773652061663696685487)
  ·
    refine ⟨4837160478092495545028231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3224773652061663696685487 4837160478092495545028231)
    ·
      refine ⟨7255740717138743317542347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4837160478092495545028231 7255740717138743317542347)
      ·
        refine ⟨10883611075708114976313521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7255740717138743317542347 10883611075708114976313521)
        ·
          refine ⟨8162708306781086232235141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10883611075708114976313521 8162708306781086232235141)
          ·
            refine ⟨1530507807521453668544089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8162708306781086232235141 1530507807521453668544089)
            ·
              refine ⟨1147880855641090251408067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530507807521453668544089 1147880855641090251408067)
              ·
                refine ⟨1721821283461635377112101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147880855641090251408067 1721821283461635377112101)
                ·
                  refine ⟨322841490649056633208519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721821283461635377112101 322841490649056633208519)
                  ·
                    rfl

theorem cell21_1414646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1414646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414646 prefixEnd_1414646 := by exact prefixLift 1414646
  have htrace : WordTrace (prefixWord ++ tailWord_1414646) baseStart_1414646 baseEnd_1414646 := by
    simpa [prefixWord, tailWord_1414646, baseEnd_1414646] using wordTrace_append hprefix tailTrace_1414646
  have hstable : (prefixWord ++ tailWord_1414646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414646).length < 2 ^ (prefixWord ++ tailWord_1414646).sum := by decide
  have hdescent : baseEnd_1414646 < baseStart_1414646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414688 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_1414688 : Nat := 118140960795 + 1414688 * 2 ^ 59
def prefixEnd_1414688 : Nat := 4983230072969 + 3 ^ 40 * 1414688 * 2
def baseEnd_1414688 : Nat := 322851075621273893508433

theorem tailTrace_1414688 : CollatzResearch.WordTrace tailWord_1414688 prefixEnd_1414688 322851075621273893508433 := by
  unfold tailWord_1414688
  simp only [CollatzResearch.WordTrace]
  refine ⟨25798955149417230159998359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34398606865889640213331145 25798955149417230159998359)
  ·
    refine ⟨38698432724125845239997539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25798955149417230159998359 38698432724125845239997539)
    ·
      refine ⟨58047649086188767859996309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38698432724125845239997539 58047649086188767859996309)
      ·
        refine ⟨2720983550915098493437327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58047649086188767859996309 2720983550915098493437327)
        ·
          refine ⟨4081475326372647740155991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2720983550915098493437327 4081475326372647740155991)
          ·
            refine ⟨6122212989558971610233987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4081475326372647740155991 6122212989558971610233987)
            ·
              refine ⟨9183319484338457415350981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6122212989558971610233987 9183319484338457415350981)
              ·
                refine ⟨1721872403313460765378309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9183319484338457415350981 1721872403313460765378309)
                ·
                  refine ⟨322851075621273893508433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721872403313460765378309 322851075621273893508433)
                  ·
                    rfl

theorem cell21_1414688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_1414688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414688 prefixEnd_1414688 := by exact prefixLift 1414688
  have htrace : WordTrace (prefixWord ++ tailWord_1414688) baseStart_1414688 baseEnd_1414688 := by
    simpa [prefixWord, tailWord_1414688, baseEnd_1414688] using wordTrace_append hprefix tailTrace_1414688
  have hstable : (prefixWord ++ tailWord_1414688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414688).length < 2 ^ (prefixWord ++ tailWord_1414688).sum := by decide
  have hdescent : baseEnd_1414688 < baseStart_1414688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414815 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 4]
def baseStart_1414815 : Nat := 118140960795 + 1414815 * 2 ^ 59
def prefixEnd_1414815 : Nat := 4983230072969 + 3 ^ 40 * 1414815 * 2
def baseEnd_1414815 : Nat := 322880058751549894891507

theorem tailTrace_1414815 : CollatzResearch.WordTrace tailWord_1414815 prefixEnd_1414815 322880058751549894891507 := by
  unfold tailWord_1414815
  simp only [CollatzResearch.WordTrace]
  refine ⟨51602542369374361009869899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34401694912916240673246599 51602542369374361009869899)
  ·
    refine ⟨77403813554061541514804849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51602542369374361009869899 77403813554061541514804849)
    ·
      refine ⟨58052860165546156136103637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77403813554061541514804849 58052860165546156136103637)
      ·
        refine ⟨1360613910129988034439929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 58052860165546156136103637 1360613910129988034439929)
        ·
          refine ⟨1020460432597491025829947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1360613910129988034439929 1020460432597491025829947)
          ·
            refine ⟨1530690648896236538744921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020460432597491025829947 1530690648896236538744921)
            ·
              refine ⟨1148017986672177404058691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530690648896236538744921 1148017986672177404058691)
              ·
                refine ⟨1722026980008266106088037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148017986672177404058691 1722026980008266106088037)
                ·
                  refine ⟨322880058751549894891507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1722026980008266106088037 322880058751549894891507)
                  ·
                    rfl

theorem cell21_1414815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 4].length) (baseStart_1414815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414815 prefixEnd_1414815 := by exact prefixLift 1414815
  have htrace : WordTrace (prefixWord ++ tailWord_1414815) baseStart_1414815 baseEnd_1414815 := by
    simpa [prefixWord, tailWord_1414815, baseEnd_1414815] using wordTrace_append hprefix tailTrace_1414815
  have hstable : (prefixWord ++ tailWord_1414815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414815).length < 2 ^ (prefixWord ++ tailWord_1414815).sum := by decide
  have hdescent : baseEnd_1414815 < baseStart_1414815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414860 : List Nat := [2, 2, 1, 5, 2, 2, 2, 2, 3]
def baseStart_1414860 : Nat := 118140960795 + 1414860 * 2 ^ 59
def prefixEnd_1414860 : Nat := 4983230072969 + 3 ^ 40 * 1414860 * 2
def baseEnd_1414860 : Nat := 322890328364639816641415

theorem tailTrace_1414860 : CollatzResearch.WordTrace tailWord_1414860 prefixEnd_1414860 322890328364639816641415 := by
  unfold tailWord_1414860
  simp only [CollatzResearch.WordTrace]
  refine ⟨25802091827105666847629017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34402789102807555796838689 25802091827105666847629017)
  ·
    refine ⟨19351568870329250135721763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25802091827105666847629017 19351568870329250135721763)
    ·
      refine ⟨29027353305493875203582645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19351568870329250135721763 29027353305493875203582645)
      ·
        refine ⟨2721314372390050800335873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29027353305493875203582645 2721314372390050800335873)
        ·
          refine ⟨2040985779292538100251905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2721314372390050800335873 2040985779292538100251905)
          ·
            refine ⟨1530739334469403575188929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2040985779292538100251905 1530739334469403575188929)
            ·
              refine ⟨1148054500852052681391697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530739334469403575188929 1148054500852052681391697)
              ·
                refine ⟨861040875639039511043773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148054500852052681391697 861040875639039511043773)
                ·
                  refine ⟨322890328364639816641415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861040875639039511043773 322890328364639816641415)
                  ·
                    rfl

theorem cell21_1414860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_1414860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414860 prefixEnd_1414860 := by exact prefixLift 1414860
  have htrace : WordTrace (prefixWord ++ tailWord_1414860) baseStart_1414860 baseEnd_1414860 := by
    simpa [prefixWord, tailWord_1414860, baseEnd_1414860] using wordTrace_append hprefix tailTrace_1414860
  have hstable : (prefixWord ++ tailWord_1414860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414860).length < 2 ^ (prefixWord ++ tailWord_1414860).sum := by decide
  have hdescent : baseEnd_1414860 < baseStart_1414860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414902 : List Nat := [5, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_1414902 : Nat := 118140960795 + 1414902 * 2 ^ 59
def prefixEnd_1414902 : Nat := 4983230072969 + 3 ^ 40 * 1414902 * 2
def baseEnd_1414902 : Nat := 322899913336857076941329

theorem tailTrace_1414902 : CollatzResearch.WordTrace tailWord_1414902 prefixEnd_1414902 322899913336857076941329 := by
  unfold tailWord_1414902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225357220003698429267935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34403810346706116578857973 3225357220003698429267935)
  ·
    refine ⟨4838035830005547643901903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3225357220003698429267935 4838035830005547643901903)
    ·
      refine ⟨7257053745008321465852855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4838035830005547643901903 7257053745008321465852855)
      ·
        refine ⟨10885580617512482198779283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7257053745008321465852855 10885580617512482198779283)
        ·
          refine ⟨16328370926268723298168925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10885580617512482198779283 16328370926268723298168925)
          ·
            refine ⟨6123139097350771236813347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16328370926268723298168925 6123139097350771236813347)
            ·
              refine ⟨9184708646026156855220021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6123139097350771236813347 9184708646026156855220021)
              ·
                refine ⟨861066435564952205176877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9184708646026156855220021 861066435564952205176877)
                ·
                  refine ⟨322899913336857076941329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861066435564952205176877 322899913336857076941329)
                  ·
                    rfl

theorem cell21_1414902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_1414902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414902 prefixEnd_1414902 := by exact prefixLift 1414902
  have htrace : WordTrace (prefixWord ++ tailWord_1414902) baseStart_1414902 baseEnd_1414902 := by
    simpa [prefixWord, tailWord_1414902, baseEnd_1414902] using wordTrace_append hprefix tailTrace_1414902
  have hstable : (prefixWord ++ tailWord_1414902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414902).length < 2 ^ (prefixWord ++ tailWord_1414902).sum := by decide
  have hdescent : baseEnd_1414902 < baseStart_1414902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414916 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1414916 : Nat := 118140960795 + 1414916 * 2 ^ 59
def prefixEnd_1414916 : Nat := 4983230072969 + 3 ^ 40 * 1414916 * 2
def baseEnd_1414916 : Nat := 322903108327596163707967

theorem tailTrace_1414916 : CollatzResearch.WordTrace tailWord_1414916 prefixEnd_1414916 322903108327596163707967 := by
  unfold tailWord_1414916
  simp only [CollatzResearch.WordTrace]
  refine ⟨25803113071004227629648301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34404150761338970172864401 25803113071004227629648301)
  ·
    refine ⟨9676167401626585361118113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25803113071004227629648301 9676167401626585361118113)
    ·
      refine ⟨7257125551219939020838585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9676167401626585361118113 7257125551219939020838585)
      ·
        refine ⟨5442844163414954265628939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7257125551219939020838585 5442844163414954265628939)
        ·
          refine ⟨8164266245122431398443409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5442844163414954265628939 8164266245122431398443409)
          ·
            refine ⟨6123199683841823548832557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8164266245122431398443409 6123199683841823548832557)
            ·
              refine ⟨2296199881440683830812209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6123199683841823548832557 2296199881440683830812209)
              ·
                refine ⟨1722149911080512873109157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296199881440683830812209 1722149911080512873109157)
                ·
                  refine ⟨322903108327596163707967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1722149911080512873109157 322903108327596163707967)
                  ·
                    rfl

theorem cell21_1414916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1414916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414916 prefixEnd_1414916 := by exact prefixLift 1414916
  have htrace : WordTrace (prefixWord ++ tailWord_1414916) baseStart_1414916 baseEnd_1414916 := by
    simpa [prefixWord, tailWord_1414916, baseEnd_1414916] using wordTrace_append hprefix tailTrace_1414916
  have hstable : (prefixWord ++ tailWord_1414916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414916).length < 2 ^ (prefixWord ++ tailWord_1414916).sum := by decide
  have hdescent : baseEnd_1414916 < baseStart_1414916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414944 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_1414944 : Nat := 118140960795 + 1414944 * 2 ^ 59
def prefixEnd_1414944 : Nat := 4983230072969 + 3 ^ 40 * 1414944 * 2
def baseEnd_1414944 : Nat := 322909498309074337241243

theorem tailTrace_1414944 : CollatzResearch.WordTrace tailWord_1414944 prefixEnd_1414944 322909498309074337241243 := by
  unfold tailWord_1414944
  simp only [CollatzResearch.WordTrace]
  refine ⟨25803623692953508020657943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34404831590604677360877257 25803623692953508020657943)
  ·
    refine ⟨38705435539430262030986915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25803623692953508020657943 38705435539430262030986915)
    ·
      refine ⟨58058153309145393046480373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38705435539430262030986915 58058153309145393046480373)
      ·
        refine ⟨5442951872732380598107535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58058153309145393046480373 5442951872732380598107535)
        ·
          refine ⟨8164427809098570897161303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5442951872732380598107535 8164427809098570897161303)
          ·
            refine ⟨12246641713647856345741955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8164427809098570897161303 12246641713647856345741955)
            ·
              refine ⟨18369962570471784518612933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12246641713647856345741955 18369962570471784518612933)
              ·
                refine ⟨3444367981963459597239925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18369962570471784518612933 3444367981963459597239925)
                ·
                  refine ⟨322909498309074337241243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3444367981963459597239925 322909498309074337241243)
                  ·
                    rfl

theorem cell21_1414944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_1414944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1414944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1414944 prefixEnd_1414944 := by exact prefixLift 1414944
  have htrace : WordTrace (prefixWord ++ tailWord_1414944) baseStart_1414944 baseEnd_1414944 := by
    simpa [prefixWord, tailWord_1414944, baseEnd_1414944] using wordTrace_append hprefix tailTrace_1414944
  have hstable : (prefixWord ++ tailWord_1414944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414944).length < 2 ^ (prefixWord ++ tailWord_1414944).sum := by decide
  have hdescent : baseEnd_1414944 < baseStart_1414944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415034 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_1415034 : Nat := 118140960795 + 1415034 * 2 ^ 59
def prefixEnd_1415034 : Nat := 4983230072969 + 3 ^ 40 * 1415034 * 2
def baseEnd_1415034 : Nat := 322930037535254180741059

theorem tailTrace_1415034 : CollatzResearch.WordTrace tailWord_1415034 prefixEnd_1415034 322930037535254180741059 := by
  unfold tailWord_1415034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12902632488895240353023039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34407019970387307608061437 12902632488895240353023039)
  ·
    refine ⟨19353948733342860529534559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12902632488895240353023039 19353948733342860529534559)
    ·
      refine ⟨29030923100014290794301839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19353948733342860529534559 29030923100014290794301839)
      ·
        refine ⟨43546384650021436191452759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29030923100014290794301839 43546384650021436191452759)
        ·
          refine ⟨65319576975032154287179139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43546384650021436191452759 65319576975032154287179139)
          ·
            refine ⟨97979365462548231430768709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65319576975032154287179139 97979365462548231430768709)
            ·
              refine ⟨18371131024227793393269133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97979365462548231430768709 18371131024227793393269133)
              ·
                refine ⟨6889174134085422522475925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18371131024227793393269133 6889174134085422522475925)
                ·
                  refine ⟨322930037535254180741059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6889174134085422522475925 322930037535254180741059)
                  ·
                    rfl

theorem cell21_1415034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_1415034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415034 prefixEnd_1415034 := by exact prefixLift 1415034
  have htrace : WordTrace (prefixWord ++ tailWord_1415034) baseStart_1415034 baseEnd_1415034 := by
    simpa [prefixWord, tailWord_1415034, baseEnd_1415034] using wordTrace_append hprefix tailTrace_1415034
  have hstable : (prefixWord ++ tailWord_1415034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415034).length < 2 ^ (prefixWord ++ tailWord_1415034).sum := by decide
  have hdescent : baseEnd_1415034 < baseStart_1415034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415054 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_1415054 : Nat := 118140960795 + 1415054 * 2 ^ 59
def prefixEnd_1415054 : Nat := 4983230072969 + 3 ^ 40 * 1415054 * 2
def baseEnd_1415054 : Nat := 322934601807738590407685

theorem tailTrace_1415054 : CollatzResearch.WordTrace tailWord_1415054 prefixEnd_1415054 322934601807738590407685 := by
  unfold tailWord_1415054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451407426938563103477527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34407506277005669885213477 6451407426938563103477527)
  ·
    refine ⟨9677111140407844655216291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6451407426938563103477527 9677111140407844655216291)
    ·
      refine ⟨14515666710611766982824437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9677111140407844655216291 14515666710611766982824437)
      ·
        refine ⟨1360843754119853154639791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14515666710611766982824437 1360843754119853154639791)
        ·
          refine ⟨2041265631179779731959687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360843754119853154639791 2041265631179779731959687)
          ·
            refine ⟨3061898446769669597939531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041265631179779731959687 3061898446769669597939531)
            ·
              refine ⟨4592847670154504396909297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061898446769669597939531 4592847670154504396909297)
              ·
                refine ⟨3444635752615878297681973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4592847670154504396909297 3444635752615878297681973)
                ·
                  refine ⟨322934601807738590407685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3444635752615878297681973 322934601807738590407685)
                  ·
                    rfl

theorem cell21_1415054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_1415054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415054 prefixEnd_1415054 := by exact prefixLift 1415054
  have htrace : WordTrace (prefixWord ++ tailWord_1415054) baseStart_1415054 baseEnd_1415054 := by
    simpa [prefixWord, tailWord_1415054, baseEnd_1415054] using wordTrace_append hprefix tailTrace_1415054
  have hstable : (prefixWord ++ tailWord_1415054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415054).length < 2 ^ (prefixWord ++ tailWord_1415054).sum := by decide
  have hdescent : baseEnd_1415054 < baseStart_1415054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415096 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_1415096 : Nat := 118140960795 + 1415096 * 2 ^ 59
def prefixEnd_1415096 : Nat := 4983230072969 + 3 ^ 40 * 1415096 * 2
def baseEnd_1415096 : Nat := 322944186779955850707599

theorem tailTrace_1415096 : CollatzResearch.WordTrace tailWord_1415096 prefixEnd_1415096 322944186779955850707599 := by
  unfold tailWord_1415096
  simp only [CollatzResearch.WordTrace]
  refine ⟨25806395640678173000424571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34408527520904230667232761 25806395640678173000424571)
  ·
    refine ⟨38709593461017259500636857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25806395640678173000424571 38709593461017259500636857)
    ·
      refine ⟨29032195095762944625477643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38709593461017259500636857 29032195095762944625477643)
      ·
        refine ⟨43548292643644416938216465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29032195095762944625477643 43548292643644416938216465)
        ·
          refine ⟨32661219482733312703662349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43548292643644416938216465 32661219482733312703662349)
          ·
            refine ⟨12247957306024992263873381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32661219482733312703662349 12247957306024992263873381)
            ·
              refine ⟨2296491994879686049476259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12247957306024992263873381 2296491994879686049476259)
              ·
                refine ⟨3444737992319529074214389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2296491994879686049476259 3444737992319529074214389)
                ·
                  refine ⟨322944186779955850707599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3444737992319529074214389 322944186779955850707599)
                  ·
                    rfl

theorem cell21_1415096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_1415096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415096 prefixEnd_1415096 := by exact prefixLift 1415096
  have htrace : WordTrace (prefixWord ++ tailWord_1415096) baseStart_1415096 baseEnd_1415096 := by
    simpa [prefixWord, tailWord_1415096, baseEnd_1415096] using wordTrace_append hprefix tailTrace_1415096
  have hstable : (prefixWord ++ tailWord_1415096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415096).length < 2 ^ (prefixWord ++ tailWord_1415096).sum := by decide
  have hdescent : baseEnd_1415096 < baseStart_1415096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415200 : List Nat := [2, 1, 1, 17]
def baseStart_1415200 : Nat := 118140960795 + 1415200 * 2 ^ 59
def prefixEnd_1415200 : Nat := 4983230072969 + 3 ^ 40 * 1415200 * 2
def baseEnd_1415200 : Nat := 1329086094637344777671

theorem tailTrace_1415200 : CollatzResearch.WordTrace tailWord_1415200 prefixEnd_1415200 1329086094637344777671 := by
  unfold tailWord_1415200
  simp only [CollatzResearch.WordTrace]
  refine ⟨25808292236489785881317527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34411056315319714508423369 25808292236489785881317527)
  ·
    refine ⟨38712438354734678821976291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25808292236489785881317527 38712438354734678821976291)
    ·
      refine ⟨58068657532102018232964437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38712438354734678821976291 58068657532102018232964437)
      ·
        refine ⟨1329086094637344777671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 58068657532102018232964437 1329086094637344777671)
        ·
          rfl

theorem cell21_1415200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 17].length) (baseStart_1415200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415200 prefixEnd_1415200 := by exact prefixLift 1415200
  have htrace : WordTrace (prefixWord ++ tailWord_1415200) baseStart_1415200 baseEnd_1415200 := by
    simpa [prefixWord, tailWord_1415200, baseEnd_1415200] using wordTrace_append hprefix tailTrace_1415200
  have hstable : (prefixWord ++ tailWord_1415200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415200).length < 2 ^ (prefixWord ++ tailWord_1415200).sum := by decide
  have hdescent : baseEnd_1415200 < baseStart_1415200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415203 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 4]
def baseStart_1415203 : Nat := 118140960795 + 1415203 * 2 ^ 59
def prefixEnd_1415203 : Nat := 4983230072969 + 3 ^ 40 * 1415203 * 2
def baseEnd_1415203 : Nat := 322968605637747442424047

theorem tailTrace_1415203 : CollatzResearch.WordTrace tailWord_1415203 prefixEnd_1415203 322968605637747442424047 := by
  unfold tailWord_1415203
  simp only [CollatzResearch.WordTrace]
  refine ⟨51616693891968703274994263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34411129261312468849996175 51616693891968703274994263)
  ·
    refine ⟨77425040837953054912491395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51616693891968703274994263 77425040837953054912491395)
    ·
      refine ⟨116137561256929582368737093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77425040837953054912491395 116137561256929582368737093)
      ·
        refine ⟨21775792735674296694138205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116137561256929582368737093 21775792735674296694138205)
        ·
          refine ⟨8165922275877861260301827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21775792735674296694138205 8165922275877861260301827)
          ·
            refine ⟨12248883413816791890452741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8165922275877861260301827 12248883413816791890452741)
            ·
              refine ⟨2296665640090648479459889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12248883413816791890452741 2296665640090648479459889)
              ·
                refine ⟨1722499230067986359594917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296665640090648479459889 1722499230067986359594917)
                ·
                  refine ⟨322968605637747442424047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1722499230067986359594917 322968605637747442424047)
                  ·
                    rfl

theorem cell21_1415203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 4].length) (baseStart_1415203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415203 prefixEnd_1415203 := by exact prefixLift 1415203
  have htrace : WordTrace (prefixWord ++ tailWord_1415203) baseStart_1415203 baseEnd_1415203 := by
    simpa [prefixWord, tailWord_1415203, baseEnd_1415203] using wordTrace_append hprefix tailTrace_1415203
  have hstable : (prefixWord ++ tailWord_1415203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415203).length < 2 ^ (prefixWord ++ tailWord_1415203).sum := by decide
  have hdescent : baseEnd_1415203 < baseStart_1415203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415217 : List Nat := [1, 2, 2, 3, 1, 3, 3, 6]
def baseStart_1415217 : Nat := 118140960795 + 1415217 * 2 ^ 59
def prefixEnd_1415217 : Nat := 4983230072969 + 3 ^ 40 * 1415217 * 2
def baseEnd_1415217 : Nat := 107657266876162176396895

theorem tailTrace_1415217 : CollatzResearch.WordTrace tailWord_1415217 prefixEnd_1415217 107657266876162176396895 := by
  unfold tailWord_1415217
  simp only [CollatzResearch.WordTrace]
  refine ⟨51617204513917983666003905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34411469675945322444002603 51617204513917983666003905)
  ·
    refine ⟨38712903385438487749502929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51617204513917983666003905 38712903385438487749502929)
    ·
      refine ⟨29034677539078865812127197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38712903385438487749502929 29034677539078865812127197)
      ·
        refine ⟨10888004077154574679547699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29034677539078865812127197 10888004077154574679547699)
        ·
          refine ⟨16332006115731862019321549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10888004077154574679547699 16332006115731862019321549)
          ·
            refine ⟨6124502293399448257245581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16332006115731862019321549 6124502293399448257245581)
            ·
              refine ⟨2296688360024793096467093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6124502293399448257245581 2296688360024793096467093)
              ·
                refine ⟨107657266876162176396895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2296688360024793096467093 107657266876162176396895)
                ·
                  rfl

theorem cell21_1415217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 6].length) (baseStart_1415217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415217 prefixEnd_1415217 := by exact prefixLift 1415217
  have htrace : WordTrace (prefixWord ++ tailWord_1415217) baseStart_1415217 baseEnd_1415217 := by
    simpa [prefixWord, tailWord_1415217, baseEnd_1415217] using wordTrace_append hprefix tailTrace_1415217
  have hstable : (prefixWord ++ tailWord_1415217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415217).length < 2 ^ (prefixWord ++ tailWord_1415217).sum := by decide
  have hdescent : baseEnd_1415217 < baseStart_1415217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415231 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 7]
def baseStart_1415231 : Nat := 118140960795 + 1415231 * 2 ^ 59
def prefixEnd_1415231 : Nat := 4983230072969 + 3 ^ 40 * 1415231 * 2
def baseEnd_1415231 : Nat := 322974995619225615957323

theorem tailTrace_1415231 : CollatzResearch.WordTrace tailWord_1415231 prefixEnd_1415231 322974995619225615957323 := by
  unfold tailWord_1415231
  simp only [CollatzResearch.WordTrace]
  refine ⟨51617715135867264057013547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34411810090578176038009031 51617715135867264057013547)
  ·
    refine ⟨77426572703800896085520321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51617715135867264057013547 77426572703800896085520321)
    ·
      refine ⟨58069929527850672064140241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77426572703800896085520321 58069929527850672064140241)
      ·
        refine ⟨43552447145888004048105181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58069929527850672064140241 43552447145888004048105181)
        ·
          refine ⟨16332167679708001518039443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43552447145888004048105181 16332167679708001518039443)
          ·
            refine ⟨24498251519562002277059165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16332167679708001518039443 24498251519562002277059165)
            ·
              refine ⟨9186844319835750853897187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24498251519562002277059165 9186844319835750853897187)
              ·
                refine ⟨13780266479753626280845781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9186844319835750853897187 13780266479753626280845781)
                ·
                  refine ⟨322974995619225615957323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13780266479753626280845781 322974995619225615957323)
                  ·
                    rfl

theorem cell21_1415231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_1415231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415231 prefixEnd_1415231 := by exact prefixLift 1415231
  have htrace : WordTrace (prefixWord ++ tailWord_1415231) baseStart_1415231 baseEnd_1415231 := by
    simpa [prefixWord, tailWord_1415231, baseEnd_1415231] using wordTrace_append hprefix tailTrace_1415231
  have hstable : (prefixWord ++ tailWord_1415231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415231).length < 2 ^ (prefixWord ++ tailWord_1415231).sum := by decide
  have hdescent : baseEnd_1415231 < baseStart_1415231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415254 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1415254 : Nat := 118140960795 + 1415254 * 2 ^ 59
def prefixEnd_1415254 : Nat := 4983230072969 + 3 ^ 40 * 1415254 * 2
def baseEnd_1415254 : Nat := 322980244532582687073943

theorem tailTrace_1415254 : CollatzResearch.WordTrace tailWord_1415254 prefixEnd_1415254 322980244532582687073943 := by
  unfold tailWord_1415254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3226159625923996186568801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34412369343189292656733877 3226159625923996186568801)
  ·
    refine ⟨2419619719442997139926601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3226159625923996186568801 2419619719442997139926601)
    ·
      refine ⟨1814714789582247854944951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2419619719442997139926601 1814714789582247854944951)
      ·
        refine ⟨2722072184373371782417427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814714789582247854944951 2722072184373371782417427)
        ·
          refine ⟨4083108276560057673626141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722072184373371782417427 4083108276560057673626141)
          ·
            refine ⟨1531165603710021627609803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4083108276560057673626141 1531165603710021627609803)
            ·
              refine ⟨2296748405565032441414705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531165603710021627609803 2296748405565032441414705)
              ·
                refine ⟨1722561304173774331061029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296748405565032441414705 1722561304173774331061029)
                ·
                  refine ⟨322980244532582687073943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1722561304173774331061029 322980244532582687073943)
                  ·
                    rfl

theorem cell21_1415254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1415254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415254 prefixEnd_1415254 := by exact prefixLift 1415254
  have htrace : WordTrace (prefixWord ++ tailWord_1415254) baseStart_1415254 baseEnd_1415254 := by
    simpa [prefixWord, tailWord_1415254, baseEnd_1415254] using wordTrace_append hprefix tailTrace_1415254
  have hstable : (prefixWord ++ tailWord_1415254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415254).length < 2 ^ (prefixWord ++ tailWord_1415254).sum := by decide
  have hdescent : baseEnd_1415254 < baseStart_1415254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415293 : List Nat := [1, 4, 1, 1, 3, 3, 1, 7]
def baseStart_1415293 : Nat := 118140960795 + 1415293 * 2 ^ 59
def prefixEnd_1415293 : Nat := 4983230072969 + 3 ^ 40 * 1415293 * 2
def baseEnd_1415293 : Nat := 107663048287975761974621

theorem tailTrace_1415293 : CollatzResearch.WordTrace tailWord_1415293 prefixEnd_1415293 107663048287975761974621 := by
  unfold tailWord_1415293
  simp only [CollatzResearch.WordTrace]
  refine ⟨51619976461642648645770533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34413317641095099097180355 51619976461642648645770533)
  ·
    refine ⟨9678745586557996621081975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51619976461642648645770533 9678745586557996621081975)
    ·
      refine ⟨14518118379836994931622963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9678745586557996621081975 14518118379836994931622963)
      ·
        refine ⟨21777177569755492397434445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14518118379836994931622963 21777177569755492397434445)
        ·
          refine ⟨8166441588658309649037917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21777177569755492397434445 8166441588658309649037917)
          ·
            refine ⟨3062415595746866118389219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8166441588658309649037917 3062415595746866118389219)
            ·
              refine ⟨4593623393620299177583829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062415595746866118389219 4593623393620299177583829)
              ·
                refine ⟨107663048287975761974621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4593623393620299177583829 107663048287975761974621)
                ·
                  rfl

theorem cell21_1415293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 7].length) (baseStart_1415293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415293 prefixEnd_1415293 := by exact prefixLift 1415293
  have htrace : WordTrace (prefixWord ++ tailWord_1415293) baseStart_1415293 baseEnd_1415293 := by
    simpa [prefixWord, tailWord_1415293, baseEnd_1415293] using wordTrace_append hprefix tailTrace_1415293
  have hstable : (prefixWord ++ tailWord_1415293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415293).length < 2 ^ (prefixWord ++ tailWord_1415293).sum := by decide
  have hdescent : baseEnd_1415293 < baseStart_1415293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415310 : List Nat := [4, 1, 1, 3, 3, 2, 7]
def baseStart_1415310 : Nat := 118140960795 + 1415310 * 2 ^ 59
def prefixEnd_1415310 : Nat := 4983230072969 + 3 ^ 40 * 1415310 * 2
def baseEnd_1415310 : Nat := 35888113832837670460055

theorem tailTrace_1415310 : CollatzResearch.WordTrace tailWord_1415310 prefixEnd_1415310 35888113832837670460055 := by
  unfold tailWord_1415310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6452574562822632568642423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34413731001720707032759589 6452574562822632568642423)
  ·
    refine ⟨9678861844233948852963635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6452574562822632568642423 9678861844233948852963635)
    ·
      refine ⟨14518292766350923279445453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9678861844233948852963635 14518292766350923279445453)
      ·
        refine ⟨5444359787381596229792045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14518292766350923279445453 5444359787381596229792045)
        ·
          refine ⟨2041634920268098586172017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5444359787381596229792045 2041634920268098586172017)
          ·
            refine ⟨1531226190201073939629013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041634920268098586172017 1531226190201073939629013)
            ·
              refine ⟨35888113832837670460055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1531226190201073939629013 35888113832837670460055)
              ·
                rfl

theorem cell21_1415310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 7].length) (baseStart_1415310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415310 prefixEnd_1415310 := by exact prefixLift 1415310
  have htrace : WordTrace (prefixWord ++ tailWord_1415310) baseStart_1415310 baseEnd_1415310 := by
    simpa [prefixWord, tailWord_1415310, baseEnd_1415310] using wordTrace_append hprefix tailTrace_1415310
  have hstable : (prefixWord ++ tailWord_1415310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415310).length < 2 ^ (prefixWord ++ tailWord_1415310).sum := by decide
  have hdescent : baseEnd_1415310 < baseStart_1415310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415316 : List Nat := [2, 4, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1415316 : Nat := 118140960795 + 1415316 * 2 ^ 59
def prefixEnd_1415316 : Nat := 4983230072969 + 3 ^ 40 * 1415316 * 2
def baseEnd_1415316 : Nat := 322994393777284357040483

theorem tailTrace_1415316 : CollatzResearch.WordTrace tailWord_1415316 prefixEnd_1415316 322994393777284357040483 := by
  unfold tailWord_1415316
  simp only [CollatzResearch.WordTrace]
  refine ⟨25810407670279661786928901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34413876893706215715905201 25810407670279661786928901)
  ·
    refine ⟨4839451438177436585049169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25810407670279661786928901 4839451438177436585049169)
    ·
      refine ⟨3629588578633077438786877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4839451438177436585049169 3629588578633077438786877)
      ·
        refine ⟨1361095716987404039545079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3629588578633077438786877 1361095716987404039545079)
        ·
          refine ⟨2041643575481106059317619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361095716987404039545079 2041643575481106059317619)
          ·
            refine ⟨3062465363221659088976429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041643575481106059317619 3062465363221659088976429)
            ·
              refine ⟨1148424511208122158366161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3062465363221659088976429 1148424511208122158366161)
              ·
                refine ⟨861318383406091618774621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148424511208122158366161 861318383406091618774621)
                ·
                  refine ⟨322994393777284357040483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861318383406091618774621 322994393777284357040483)
                  ·
                    rfl

theorem cell21_1415316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1415316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415316 prefixEnd_1415316 := by exact prefixLift 1415316
  have htrace : WordTrace (prefixWord ++ tailWord_1415316) baseStart_1415316 baseEnd_1415316 := by
    simpa [prefixWord, tailWord_1415316, baseEnd_1415316] using wordTrace_append hprefix tailTrace_1415316
  have hstable : (prefixWord ++ tailWord_1415316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415316).length < 2 ^ (prefixWord ++ tailWord_1415316).sum := by decide
  have hdescent : baseEnd_1415316 < baseStart_1415316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415352 : List Nat := [2, 1, 2, 1, 2, 1, 3, 9]
def baseStart_1415352 : Nat := 118140960795 + 1415352 * 2 ^ 59
def prefixEnd_1415352 : Nat := 4983230072969 + 3 ^ 40 * 1415352 * 2
def baseEnd_1415352 : Nat := 107667536489252098146803

theorem tailTrace_1415352 : CollatzResearch.WordTrace tailWord_1415352 prefixEnd_1415352 107667536489252098146803 := by
  unfold tailWord_1415352
  simp only [CollatzResearch.WordTrace]
  refine ⟨25811064184214450861084155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34414752245619267814778873 25811064184214450861084155)
  ·
    refine ⟨38716596276321676291626233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25811064184214450861084155 38716596276321676291626233)
    ·
      refine ⟨29037447207241257218719675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38716596276321676291626233 29037447207241257218719675)
      ·
        refine ⟨43556170810861885828079513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29037447207241257218719675 43556170810861885828079513)
        ·
          refine ⟨32667128108146414371059635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43556170810861885828079513 32667128108146414371059635)
          ·
            refine ⟨49000692162219621556589453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32667128108146414371059635 49000692162219621556589453)
            ·
              refine ⟨18375259560832358083721045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49000692162219621556589453 18375259560832358083721045)
              ·
                refine ⟨107667536489252098146803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18375259560832358083721045 107667536489252098146803)
                ·
                  rfl

theorem cell21_1415352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_1415352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415352 prefixEnd_1415352 := by exact prefixLift 1415352
  have htrace : WordTrace (prefixWord ++ tailWord_1415352) baseStart_1415352 baseEnd_1415352 := by
    simpa [prefixWord, tailWord_1415352, baseEnd_1415352] using wordTrace_append hprefix tailTrace_1415352
  have hstable : (prefixWord ++ tailWord_1415352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415352).length < 2 ^ (prefixWord ++ tailWord_1415352).sum := by decide
  have hdescent : baseEnd_1415352 < baseStart_1415352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415383 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 5]
def baseStart_1415383 : Nat := 118140960795 + 1415383 * 2 ^ 59
def prefixEnd_1415383 : Nat := 4983230072969 + 3 ^ 40 * 1415383 * 2
def baseEnd_1415383 : Nat := 323009684090107129423679

theorem tailTrace_1415383 : CollatzResearch.WordTrace tailWord_1415383 prefixEnd_1415383 323009684090107129423679 := by
  unfold tailWord_1415383
  simp only [CollatzResearch.WordTrace]
  refine ⟨51623259031316594016546803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34415506020877729344364535 51623259031316594016546803)
  ·
    refine ⟨77434888546974891024820205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51623259031316594016546803 77434888546974891024820205)
    ·
      refine ⟨29038083205115584134307577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77434888546974891024820205 29038083205115584134307577)
      ·
        refine ⟨21778562403836688100730683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29038083205115584134307577 21778562403836688100730683)
        ·
          refine ⟨32667843605755032151096025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21778562403836688100730683 32667843605755032151096025)
          ·
            refine ⟨24500882704316274113322019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32667843605755032151096025 24500882704316274113322019)
            ·
              refine ⟨36751324056474411169983029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24500882704316274113322019 36751324056474411169983029)
              ·
                refine ⟨3445436630294476047185909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36751324056474411169983029 3445436630294476047185909)
                ·
                  refine ⟨323009684090107129423679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3445436630294476047185909 323009684090107129423679)
                  ·
                    rfl

theorem cell21_1415383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_1415383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415383 prefixEnd_1415383 := by exact prefixLift 1415383
  have htrace : WordTrace (prefixWord ++ tailWord_1415383) baseStart_1415383 baseEnd_1415383 := by
    simpa [prefixWord, tailWord_1415383, baseEnd_1415383] using wordTrace_append hprefix tailTrace_1415383
  have hstable : (prefixWord ++ tailWord_1415383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415383).length < 2 ^ (prefixWord ++ tailWord_1415383).sum := by decide
  have hdescent : baseEnd_1415383 < baseStart_1415383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415400 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_1415400 : Nat := 118140960795 + 1415400 * 2 ^ 59
def prefixEnd_1415400 : Nat := 4983230072969 + 3 ^ 40 * 1415400 * 2
def baseEnd_1415400 : Nat := 323013563721718877640311

theorem tailTrace_1415400 : CollatzResearch.WordTrace tailWord_1415400 prefixEnd_1415400 323013563721718877640311 := by
  unfold tailWord_1415400
  simp only [CollatzResearch.WordTrace]
  refine ⟨25811939536127502959957827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34415919381503337279943769 25811939536127502959957827)
  ·
    refine ⟨38717909304191254439936741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25811939536127502959957827 38717909304191254439936741)
    ·
      refine ⟨7259607994535860207488139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38717909304191254439936741 7259607994535860207488139)
      ·
        refine ⟨10889411991803790311232209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259607994535860207488139 10889411991803790311232209)
        ·
          refine ⟨8167058993852842733424157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10889411991803790311232209 8167058993852842733424157)
          ·
            refine ⟨3062647122694816025034059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8167058993852842733424157 3062647122694816025034059)
            ·
              refine ⟨4593970684042224037551089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062647122694816025034059 4593970684042224037551089)
              ·
                refine ⟨3445478013031668028163317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4593970684042224037551089 3445478013031668028163317)
                ·
                  refine ⟨323013563721718877640311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3445478013031668028163317 323013563721718877640311)
                  ·
                    rfl

theorem cell21_1415400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_1415400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415400 prefixEnd_1415400 := by exact prefixLift 1415400
  have htrace : WordTrace (prefixWord ++ tailWord_1415400) baseStart_1415400 baseEnd_1415400 := by
    simpa [prefixWord, tailWord_1415400, baseEnd_1415400] using wordTrace_append hprefix tailTrace_1415400
  have hstable : (prefixWord ++ tailWord_1415400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415400).length < 2 ^ (prefixWord ++ tailWord_1415400).sum := by decide
  have hdescent : baseEnd_1415400 < baseStart_1415400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415459 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 5]
def baseStart_1415459 : Nat := 118140960795 + 1415459 * 2 ^ 59
def prefixEnd_1415459 : Nat := 4983230072969 + 3 ^ 40 * 1415459 * 2
def baseEnd_1415459 : Nat := 323027028325547886156857

theorem tailTrace_1415459 : CollatzResearch.WordTrace tailWord_1415459 prefixEnd_1415459 323027028325547886156857 := by
  unfold tailWord_1415459
  simp only [CollatzResearch.WordTrace]
  refine ⟨51626030979041258996313431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34417353986027505997542287 51626030979041258996313431)
  ·
    refine ⟨77439046468561888494470147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51626030979041258996313431 77439046468561888494470147)
    ·
      refine ⟨116158569702842832741705221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77439046468561888494470147 116158569702842832741705221)
      ·
        refine ⟨21779731819283031139069729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116158569702842832741705221 21779731819283031139069729)
        ·
          refine ⟨16334798864462273354302297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21779731819283031139069729 16334798864462273354302297)
          ·
            refine ⟨12251099148346705015726723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16334798864462273354302297 12251099148346705015726723)
            ·
              refine ⟨18376648722520057523590085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12251099148346705015726723 18376648722520057523590085)
              ·
                refine ⟨3445621635472510785673141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18376648722520057523590085 3445621635472510785673141)
                ·
                  refine ⟨323027028325547886156857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3445621635472510785673141 323027028325547886156857)
                  ·
                    rfl

theorem cell21_1415459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_1415459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415459 prefixEnd_1415459 := by exact prefixLift 1415459
  have htrace : WordTrace (prefixWord ++ tailWord_1415459) baseStart_1415459 baseEnd_1415459 := by
    simpa [prefixWord, tailWord_1415459, baseEnd_1415459] using wordTrace_append hprefix tailTrace_1415459
  have hstable : (prefixWord ++ tailWord_1415459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415459).length < 2 ^ (prefixWord ++ tailWord_1415459).sum := by decide
  have hdescent : baseEnd_1415459 < baseStart_1415459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415504 : List Nat := [2, 1, 1, 1, 1, 6, 1, 8]
def baseStart_1415504 : Nat := 118140960795 + 1415504 * 2 ^ 59
def prefixEnd_1415504 : Nat := 4983230072969 + 3 ^ 40 * 1415504 * 2
def baseEnd_1415504 : Nat := 107679099312879269302255

theorem tailTrace_1415504 : CollatzResearch.WordTrace tailWord_1415504 prefixEnd_1415504 107679099312879269302255 := by
  unfold tailWord_1415504
  simp only [CollatzResearch.WordTrace]
  refine ⟨25813836131939115840850783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34418448175918821121134377 25813836131939115840850783)
  ·
    refine ⟨38720754197908673761276175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25813836131939115840850783 38720754197908673761276175)
    ·
      refine ⟨58081131296863010641914263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38720754197908673761276175 58081131296863010641914263)
      ·
        refine ⟨87121696945294515962871395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58081131296863010641914263 87121696945294515962871395)
        ·
          refine ⟨130682545417941773944307093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87121696945294515962871395 130682545417941773944307093)
          ·
            refine ⟨6125744316466020653639395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130682545417941773944307093 6125744316466020653639395)
            ·
              refine ⟨9188616474699030980459093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6125744316466020653639395 9188616474699030980459093)
              ·
                refine ⟨107679099312879269302255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9188616474699030980459093 107679099312879269302255)
                ·
                  rfl

theorem cell21_1415504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_1415504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415504 prefixEnd_1415504 := by exact prefixLift 1415504
  have htrace : WordTrace (prefixWord ++ tailWord_1415504) baseStart_1415504 baseEnd_1415504 := by
    simpa [prefixWord, tailWord_1415504, baseEnd_1415504] using wordTrace_append hprefix tailTrace_1415504
  have hstable : (prefixWord ++ tailWord_1415504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415504).length < 2 ^ (prefixWord ++ tailWord_1415504).sum := by decide
  have hdescent : baseEnd_1415504 < baseStart_1415504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415656 : List Nat := [2, 1, 4, 1, 1, 3, 9]
def baseStart_1415656 : Nat := 118140960795 + 1415656 * 2 ^ 59
def prefixEnd_1415656 : Nat := 4983230072969 + 3 ^ 40 * 1415656 * 2
def baseEnd_1415656 : Nat := 35896887378835480152569

theorem tailTrace_1415656 : CollatzResearch.WordTrace tailWord_1415656 prefixEnd_1415656 35896887378835480152569 := by
  unfold tailWord_1415656
  simp only [CollatzResearch.WordTrace]
  refine ⟨25816608079663780820617411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34422144106218374427489881 25816608079663780820617411)
  ·
    refine ⟨38724912119495671230926117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25816608079663780820617411 38724912119495671230926117)
    ·
      refine ⟨7260921022405438355798647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38724912119495671230926117 7260921022405438355798647)
      ·
        refine ⟨10891381533608157533697971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7260921022405438355798647 10891381533608157533697971)
        ·
          refine ⟨16337072300412236300546957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10891381533608157533697971 16337072300412236300546957)
          ·
            refine ⟨6126402112654588612705109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16337072300412236300546957 6126402112654588612705109)
            ·
              refine ⟨35896887378835480152569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6126402112654588612705109 35896887378835480152569)
              ·
                rfl

theorem cell21_1415656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 9].length) (baseStart_1415656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415656 prefixEnd_1415656 := by exact prefixLift 1415656
  have htrace : WordTrace (prefixWord ++ tailWord_1415656) baseStart_1415656 baseEnd_1415656 := by
    simpa [prefixWord, tailWord_1415656, baseEnd_1415656] using wordTrace_append hprefix tailTrace_1415656
  have hstable : (prefixWord ++ tailWord_1415656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415656).length < 2 ^ (prefixWord ++ tailWord_1415656).sum := by decide
  have hdescent : baseEnd_1415656 < baseStart_1415656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415662 : List Nat := [4, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_1415662 : Nat := 118140960795 + 1415662 * 2 ^ 59
def prefixEnd_1415662 : Nat := 4983230072969 + 3 ^ 40 * 1415662 * 2
def baseEnd_1415662 : Nat := 323073355691264644273109

theorem tailTrace_1415662 : CollatzResearch.WordTrace tailWord_1415662 prefixEnd_1415662 323073355691264644273109 := by
  unfold tailWord_1415662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6454179374663228083244155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34422289998203883110635493 6454179374663228083244155)
  ·
    refine ⟨9681269061994842124866233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6454179374663228083244155 9681269061994842124866233)
    ·
      refine ⟨7260951796496131593649675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9681269061994842124866233 7260951796496131593649675)
      ·
        refine ⟨10891427694744197390474513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7260951796496131593649675 10891427694744197390474513)
        ·
          refine ⟨8168570771058148042855885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10891427694744197390474513 8168570771058148042855885)
          ·
            refine ⟨3063214039146805516070957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8168570771058148042855885 3063214039146805516070957)
            ·
              refine ⟨1148705264680052068526609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3063214039146805516070957 1148705264680052068526609)
              ·
                refine ⟨861528948510039051394957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148705264680052068526609 861528948510039051394957)
                ·
                  refine ⟨323073355691264644273109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861528948510039051394957 323073355691264644273109)
                  ·
                    rfl

theorem cell21_1415662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_1415662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415662 prefixEnd_1415662 := by exact prefixLift 1415662
  have htrace : WordTrace (prefixWord ++ tailWord_1415662) baseStart_1415662 baseEnd_1415662 := by
    simpa [prefixWord, tailWord_1415662, baseEnd_1415662] using wordTrace_append hprefix tailTrace_1415662
  have hstable : (prefixWord ++ tailWord_1415662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415662).length < 2 ^ (prefixWord ++ tailWord_1415662).sum := by decide
  have hdescent : baseEnd_1415662 < baseStart_1415662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415749 : List Nat := [1, 3, 1, 1, 1, 6, 3, 5]
def baseStart_1415749 : Nat := 118140960795 + 1415749 * 2 ^ 59
def prefixEnd_1415749 : Nat := 4983230072969 + 3 ^ 40 * 1415749 * 2
def baseEnd_1415749 : Nat := 107697736758857275440977

theorem tailTrace_1415749 : CollatzResearch.WordTrace tailWord_1415749 prefixEnd_1415749 107697736758857275440977 := by
  unfold tailWord_1415749
  simp only [CollatzResearch.WordTrace]
  refine ⟨51636608147990638524370301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34424405431993759016246867 51636608147990638524370301)
  ·
    refine ⟨19363728055496489446638863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51636608147990638524370301 19363728055496489446638863)
    ·
      refine ⟨29045592083244734169958295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19363728055496489446638863 29045592083244734169958295)
      ·
        refine ⟨43568388124867101254937443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29045592083244734169958295 43568388124867101254937443)
        ·
          refine ⟨65352582187300651882406165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43568388124867101254937443 65352582187300651882406165)
          ·
            refine ⟨3063402290029718056987789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65352582187300651882406165 3063402290029718056987789)
            ·
              refine ⟨1148775858761144271370421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3063402290029718056987789 1148775858761144271370421)
              ·
                refine ⟨107697736758857275440977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1148775858761144271370421 107697736758857275440977)
                ·
                  rfl

theorem cell21_1415749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 5].length) (baseStart_1415749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415749 prefixEnd_1415749 := by exact prefixLift 1415749
  have htrace : WordTrace (prefixWord ++ tailWord_1415749) baseStart_1415749 baseEnd_1415749 := by
    simpa [prefixWord, tailWord_1415749, baseEnd_1415749] using wordTrace_append hprefix tailTrace_1415749
  have hstable : (prefixWord ++ tailWord_1415749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415749).length < 2 ^ (prefixWord ++ tailWord_1415749).sum := by decide
  have hdescent : baseEnd_1415749 < baseStart_1415749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415780 : List Nat := [2, 3, 1, 1, 2, 2, 1, 6, 3]
def baseStart_1415780 : Nat := 118140960795 + 1415780 * 2 ^ 59
def prefixEnd_1415780 : Nat := 4983230072969 + 3 ^ 40 * 1415780 * 2
def baseEnd_1415780 : Nat := 323100284898922661306201

theorem tailTrace_1415780 : CollatzResearch.WordTrace tailWord_1415780 prefixEnd_1415780 323100284898922661306201 := by
  unfold tailWord_1415780
  simp only [CollatzResearch.WordTrace]
  refine ⟨25818869405439165409374397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34425159207252220545832529 25818869405439165409374397)
  ·
    refine ⟨9682076027039687028515399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25818869405439165409374397 9682076027039687028515399)
    ·
      refine ⟨14523114040559530542773099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9682076027039687028515399 14523114040559530542773099)
      ·
        refine ⟨21784671060839295814159649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14523114040559530542773099 21784671060839295814159649)
        ·
          refine ⟨16338503295629471860619737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21784671060839295814159649 16338503295629471860619737)
          ·
            refine ⟨12253877471722103895464803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16338503295629471860619737 12253877471722103895464803)
            ·
              refine ⟨18380816207583155843197205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12253877471722103895464803 18380816207583155843197205)
              ·
                refine ⟨861600759730460430149869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18380816207583155843197205 861600759730460430149869)
                ·
                  refine ⟨323100284898922661306201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861600759730460430149869 323100284898922661306201)
                  ·
                    rfl

theorem cell21_1415780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_1415780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415780 prefixEnd_1415780 := by exact prefixLift 1415780
  have htrace : WordTrace (prefixWord ++ tailWord_1415780) baseStart_1415780 baseEnd_1415780 := by
    simpa [prefixWord, tailWord_1415780, baseEnd_1415780] using wordTrace_append hprefix tailTrace_1415780
  have hstable : (prefixWord ++ tailWord_1415780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415780).length < 2 ^ (prefixWord ++ tailWord_1415780).sum := by decide
  have hdescent : baseEnd_1415780 < baseStart_1415780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415808 : List Nat := [2, 1, 1, 2, 1, 6, 1, 7]
def baseStart_1415808 : Nat := 118140960795 + 1415808 * 2 ^ 59
def prefixEnd_1415808 : Nat := 4983230072969 + 3 ^ 40 * 1415808 * 2
def baseEnd_1415808 : Nat := 107702224960133611613159

theorem tailTrace_1415808 : CollatzResearch.WordTrace tailWord_1415808 prefixEnd_1415808 107702224960133611613159 := by
  unfold tailWord_1415808
  simp only [CollatzResearch.WordTrace]
  refine ⟨25819380027388445800384039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34425840036517927733845385 25819380027388445800384039)
  ·
    refine ⟨38729070041082668700576059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25819380027388445800384039 38729070041082668700576059)
    ·
      refine ⟨58093605061624003050864089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38729070041082668700576059 58093605061624003050864089)
      ·
        refine ⟨43570203796218002288148067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58093605061624003050864089 43570203796218002288148067)
        ·
          refine ⟨65355305694327003432222101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43570203796218002288148067 65355305694327003432222101)
          ·
            refine ⟨3063529954421578285885411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65355305694327003432222101 3063529954421578285885411)
            ·
              refine ⟨4595294931632367428828117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3063529954421578285885411 4595294931632367428828117)
              ·
                refine ⟨107702224960133611613159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4595294931632367428828117 107702224960133611613159)
                ·
                  rfl

theorem cell21_1415808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_1415808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415808 prefixEnd_1415808 := by exact prefixLift 1415808
  have htrace : WordTrace (prefixWord ++ tailWord_1415808) baseStart_1415808 baseEnd_1415808 := by
    simpa [prefixWord, tailWord_1415808, baseEnd_1415808] using wordTrace_append hprefix tailTrace_1415808
  have hstable : (prefixWord ++ tailWord_1415808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415808).length < 2 ^ (prefixWord ++ tailWord_1415808).sum := by decide
  have hdescent : baseEnd_1415808 < baseStart_1415808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415884 : List Nat := [2, 2, 1, 5, 1, 10]
def baseStart_1415884 : Nat := 118140960795 + 1415884 * 2 ^ 59
def prefixEnd_1415884 : Nat := 4983230072969 + 3 ^ 40 * 1415884 * 2
def baseEnd_1415884 : Nat := 11967556263549688576765

theorem tailTrace_1415884 : CollatzResearch.WordTrace tailWord_1415884 prefixEnd_1415884 11967556263549688576765 := by
  unfold tailWord_1415884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25820766001250778290267353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34427688001667704387023137 25820766001250778290267353)
  ·
    refine ⟨19365574500938083717700515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25820766001250778290267353 19365574500938083717700515)
    ·
      refine ⟨29048361751407125576550773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19365574500938083717700515 29048361751407125576550773)
      ·
        refine ⟨2723283914194418022801635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29048361751407125576550773 2723283914194418022801635)
        ·
          refine ⟨4084925871291627034202453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723283914194418022801635 4084925871291627034202453)
          ·
            refine ⟨11967556263549688576765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4084925871291627034202453 11967556263549688576765)
            ·
              rfl

theorem cell21_1415884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 10].length) (baseStart_1415884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415884 prefixEnd_1415884 := by exact prefixLift 1415884
  have htrace : WordTrace (prefixWord ++ tailWord_1415884) baseStart_1415884 baseEnd_1415884 := by
    simpa [prefixWord, tailWord_1415884, baseEnd_1415884] using wordTrace_append hprefix tailTrace_1415884
  have hstable : (prefixWord ++ tailWord_1415884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415884).length < 2 ^ (prefixWord ++ tailWord_1415884).sum := by decide
  have hdescent : baseEnd_1415884 < baseStart_1415884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415932 : List Nat := [2, 2, 2, 1, 3, 2, 1, 5, 3]
def baseStart_1415932 : Nat := 118140960795 + 1415932 * 2 ^ 59
def prefixEnd_1415932 : Nat := 4983230072969 + 3 ^ 40 * 1415932 * 2
def baseEnd_1415932 : Nat := 323134973369804174772557

theorem tailTrace_1415932 : CollatzResearch.WordTrace tailWord_1415932 prefixEnd_1415932 323134973369804174772557 := by
  unfold tailWord_1415932
  simp only [CollatzResearch.WordTrace]
  refine ⟨25821641353163830389141025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34428855137551773852188033 25821641353163830389141025)
  ·
    refine ⟨19366231014872872791855769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25821641353163830389141025 19366231014872872791855769)
    ·
      refine ⟨14524673261154654593891827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19366231014872872791855769 14524673261154654593891827)
      ·
        refine ⟨21787009891731981890837741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14524673261154654593891827 21787009891731981890837741)
        ·
          refine ⟨8170128709399493209064153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21787009891731981890837741 8170128709399493209064153)
          ·
            refine ⟨6127596532049619906798115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8170128709399493209064153 6127596532049619906798115)
            ·
              refine ⟨9191394798074429860197173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6127596532049619906798115 9191394798074429860197173)
              ·
                refine ⟨861693262319477799393485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9191394798074429860197173 861693262319477799393485)
                ·
                  refine ⟨323134973369804174772557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861693262319477799393485 323134973369804174772557)
                  ·
                    rfl

theorem cell21_1415932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_1415932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1415932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1415932 prefixEnd_1415932 := by exact prefixLift 1415932
  have htrace : WordTrace (prefixWord ++ tailWord_1415932) baseStart_1415932 baseEnd_1415932 := by
    simpa [prefixWord, tailWord_1415932, baseEnd_1415932] using wordTrace_append hprefix tailTrace_1415932
  have hstable : (prefixWord ++ tailWord_1415932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415932).length < 2 ^ (prefixWord ++ tailWord_1415932).sum := by decide
  have hdescent : baseEnd_1415932 < baseStart_1415932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416036 : List Nat := [2, 3, 1, 1, 4, 1, 2, 7]
def baseStart_1416036 : Nat := 118140960795 + 1416036 * 2 ^ 59
def prefixEnd_1416036 : Nat := 4983230072969 + 3 ^ 40 * 1416036 * 2
def baseEnd_1416036 : Nat := 107719569195574368346337

theorem tailTrace_1416036 : CollatzResearch.WordTrace tailWord_1416036 prefixEnd_1416036 107719569195574368346337 := by
  unfold tailWord_1416036
  simp only [CollatzResearch.WordTrace]
  refine ⟨25823537948975443270033981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34431383931967257693378641 25823537948975443270033981)
  ·
    refine ⟨9683826730865791226262743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25823537948975443270033981 9683826730865791226262743)
    ·
      refine ⟨14525740096298686839394115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9683826730865791226262743 14525740096298686839394115)
      ·
        refine ⟨21788610144448030259091173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14525740096298686839394115 21788610144448030259091173)
        ·
          refine ⟨4085364402084005673579595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21788610144448030259091173 4085364402084005673579595)
          ·
            refine ⟨6128046603126008510369393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4085364402084005673579595 6128046603126008510369393)
            ·
              refine ⟨4596034952344506382777045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6128046603126008510369393 4596034952344506382777045)
              ·
                refine ⟨107719569195574368346337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4596034952344506382777045 107719569195574368346337)
                ·
                  rfl

theorem cell21_1416036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_1416036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416036 prefixEnd_1416036 := by exact prefixLift 1416036
  have htrace : WordTrace (prefixWord ++ tailWord_1416036) baseStart_1416036 baseEnd_1416036 := by
    simpa [prefixWord, tailWord_1416036, baseEnd_1416036] using wordTrace_append hprefix tailTrace_1416036
  have hstable : (prefixWord ++ tailWord_1416036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416036).length < 2 ^ (prefixWord ++ tailWord_1416036).sum := by decide
  have hdescent : baseEnd_1416036 < baseStart_1416036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416146 : List Nat := [3, 2, 2, 3, 1, 3, 2, 5]
def baseStart_1416146 : Nat := 118140960795 + 1416146 * 2 ^ 59
def prefixEnd_1416146 : Nat := 4983230072969 + 3 ^ 40 * 1416146 * 2
def baseEnd_1416146 : Nat := 107727937028462452735151

theorem tailTrace_1416146 : CollatzResearch.WordTrace tailWord_1416146 prefixEnd_1416146 107727937028462452735151 := by
  unfold tailWord_1416146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12912771981888093831643073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34434058618368250217714861 12912771981888093831643073)
  ·
    refine ⟨9684578986416070373732305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12912771981888093831643073 9684578986416070373732305)
    ·
      refine ⟨7263434239812052780299229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9684578986416070373732305 7263434239812052780299229)
      ·
        refine ⟨2723787839929519792612211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7263434239812052780299229 2723787839929519792612211)
        ·
          refine ⟨4085681759894279688918317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723787839929519792612211 4085681759894279688918317)
          ·
            refine ⟨1532130659960354883344369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4085681759894279688918317 1532130659960354883344369)
            ·
              refine ⟨1149097994970266162508277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532130659960354883344369 1149097994970266162508277)
              ·
                refine ⟨107727937028462452735151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1149097994970266162508277 107727937028462452735151)
                ·
                  rfl

theorem cell21_1416146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_1416146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416146 prefixEnd_1416146 := by exact prefixLift 1416146
  have htrace : WordTrace (prefixWord ++ tailWord_1416146) baseStart_1416146 baseEnd_1416146 := by
    simpa [prefixWord, tailWord_1416146, baseEnd_1416146] using wordTrace_append hprefix tailTrace_1416146
  have hstable : (prefixWord ++ tailWord_1416146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416146).length < 2 ^ (prefixWord ++ tailWord_1416146).sum := by decide
  have hdescent : baseEnd_1416146 < baseStart_1416146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416177 : List Nat := [1, 2, 2, 2, 4, 2, 3, 2, 3]
def baseStart_1416177 : Nat := 118140960795 + 1416177 * 2 ^ 59
def prefixEnd_1416177 : Nat := 4983230072969 + 3 ^ 40 * 1416177 * 2
def baseEnd_1416177 : Nat := 323190885707738193188723

theorem tailTrace_1416177 : CollatzResearch.WordTrace tailWord_1416177 prefixEnd_1416177 323190885707738193188723 := by
  unfold tailWord_1416177
  simp only [CollatzResearch.WordTrace]
  refine ⟨51652218590440067620950785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34434812393626711747300523 51652218590440067620950785)
  ·
    refine ⟨38739163942830050715713089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51652218590440067620950785 38739163942830050715713089)
    ·
      refine ⟨29054372957122538036784817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38739163942830050715713089 29054372957122538036784817)
      ·
        refine ⟨21790779717841903527588613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29054372957122538036784817 21790779717841903527588613)
        ·
          refine ⟨4085771197095356911422865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21790779717841903527588613 4085771197095356911422865)
          ·
            refine ⟨3064328397821517683567149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4085771197095356911422865 3064328397821517683567149)
            ·
              refine ⟨1149123149183069131337681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3064328397821517683567149 1149123149183069131337681)
              ·
                refine ⟨861842361887301848503261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149123149183069131337681 861842361887301848503261)
                ·
                  refine ⟨323190885707738193188723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861842361887301848503261 323190885707738193188723)
                  ·
                    rfl

theorem cell21_1416177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_1416177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416177 prefixEnd_1416177 := by exact prefixLift 1416177
  have htrace : WordTrace (prefixWord ++ tailWord_1416177) baseStart_1416177 baseEnd_1416177 := by
    simpa [prefixWord, tailWord_1416177, baseEnd_1416177] using wordTrace_append hprefix tailTrace_1416177
  have hstable : (prefixWord ++ tailWord_1416177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416177).length < 2 ^ (prefixWord ++ tailWord_1416177).sum := by decide
  have hdescent : baseEnd_1416177 < baseStart_1416177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416180 : List Nat := [2, 6, 2, 1, 1, 1, 2, 6]
def baseStart_1416180 : Nat := 118140960795 + 1416180 * 2 ^ 59
def prefixEnd_1416180 : Nat := 4983230072969 + 3 ^ 40 * 1416180 * 2
def baseEnd_1416180 : Nat := 107730523449536951546239

theorem tailTrace_1416180 : CollatzResearch.WordTrace tailWord_1416180 prefixEnd_1416180 107730523449536951546239 := by
  unfold tailWord_1416180
  simp only [CollatzResearch.WordTrace]
  refine ⟨25826164004714599566654997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34434885339619466088873329 25826164004714599566654997)
  ·
    refine ⟨1210601437720996854686953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25826164004714599566654997 1210601437720996854686953)
    ·
      refine ⟨907951078290747641015215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1210601437720996854686953 907951078290747641015215)
      ·
        refine ⟨1361926617436121461522823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907951078290747641015215 1361926617436121461522823)
        ·
          refine ⟨2042889926154182192284235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361926617436121461522823 2042889926154182192284235)
          ·
            refine ⟨3064334889231273288426353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042889926154182192284235 3064334889231273288426353)
            ·
              refine ⟨2298251166923454966319765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064334889231273288426353 2298251166923454966319765)
              ·
                refine ⟨107730523449536951546239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2298251166923454966319765 107730523449536951546239)
                ·
                  rfl

theorem cell21_1416180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_1416180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416180 prefixEnd_1416180 := by exact prefixLift 1416180
  have htrace : WordTrace (prefixWord ++ tailWord_1416180) baseStart_1416180 baseEnd_1416180 := by
    simpa [prefixWord, tailWord_1416180, baseEnd_1416180] using wordTrace_append hprefix tailTrace_1416180
  have hstable : (prefixWord ++ tailWord_1416180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416180).length < 2 ^ (prefixWord ++ tailWord_1416180).sum := by decide
  have hdescent : baseEnd_1416180 < baseStart_1416180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416188 : List Nat := [2, 2, 2, 1, 2, 4, 2, 6]
def baseStart_1416188 : Nat := 118140960795 + 1416188 * 2 ^ 59
def prefixEnd_1416188 : Nat := 4983230072969 + 3 ^ 40 * 1416188 * 2
def baseEnd_1416188 : Nat := 107731132019201539501789

theorem tailTrace_1416188 : CollatzResearch.WordTrace tailWord_1416188 prefixEnd_1416188 107731132019201539501789 := by
  unfold tailWord_1416188
  simp only [CollatzResearch.WordTrace]
  refine ⟨25826309896700108249800609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34435079862266810999734145 25826309896700108249800609)
  ·
    refine ⟨19369732422525081187350457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25826309896700108249800609 19369732422525081187350457)
    ·
      refine ⟨14527299316893810890512843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19369732422525081187350457 14527299316893810890512843)
      ·
        refine ⟨21790948975340716335769265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14527299316893810890512843 21790948975340716335769265)
        ·
          refine ⟨16343211731505537251826949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21790948975340716335769265 16343211731505537251826949)
          ·
            refine ⟨3064352199657288234717553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16343211731505537251826949 3064352199657288234717553)
            ·
              refine ⟨2298264149742966176038165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064352199657288234717553 2298264149742966176038165)
              ·
                refine ⟨107731132019201539501789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2298264149742966176038165 107731132019201539501789)
                ·
                  rfl

theorem cell21_1416188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_1416188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416188 prefixEnd_1416188 := by exact prefixLift 1416188
  have htrace : WordTrace (prefixWord ++ tailWord_1416188) baseStart_1416188 baseEnd_1416188 := by
    simpa [prefixWord, tailWord_1416188, baseEnd_1416188] using wordTrace_append hprefix tailTrace_1416188
  have hstable : (prefixWord ++ tailWord_1416188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416188).length < 2 ^ (prefixWord ++ tailWord_1416188).sum := by decide
  have hdescent : baseEnd_1416188 < baseStart_1416188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416264 : List Nat := [2, 1, 3, 1, 1, 1, 7, 5]
def baseStart_1416264 : Nat := 118140960795 + 1416264 * 2 ^ 59
def prefixEnd_1416264 : Nat := 4983230072969 + 3 ^ 40 * 1416264 * 2
def baseEnd_1416264 : Nat := 107736913431015125079515

theorem tailTrace_1416264 : CollatzResearch.WordTrace tailWord_1416264 prefixEnd_1416264 107736913431015125079515 := by
  unfold tailWord_1416264
  simp only [CollatzResearch.WordTrace]
  refine ⟨25827695870562440739683923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34436927827416587652911897 25827695870562440739683923)
  ·
    refine ⟨38741543805843661109525885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25827695870562440739683923 38741543805843661109525885)
    ·
      refine ⟨14528078927191372916072207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38741543805843661109525885 14528078927191372916072207)
      ·
        refine ⟨21792118390787059374108311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14528078927191372916072207 21792118390787059374108311)
        ·
          refine ⟨32688177586180589061162467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21792118390787059374108311 32688177586180589061162467)
          ·
            refine ⟨49032266379270883591743701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32688177586180589061162467 49032266379270883591743701)
            ·
              refine ⟨1149193743264161334181493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49032266379270883591743701 1149193743264161334181493)
              ·
                refine ⟨107736913431015125079515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1149193743264161334181493 107736913431015125079515)
                ·
                  rfl

theorem cell21_1416264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_1416264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416264 prefixEnd_1416264 := by exact prefixLift 1416264
  have htrace : WordTrace (prefixWord ++ tailWord_1416264) baseStart_1416264 baseEnd_1416264 := by
    simpa [prefixWord, tailWord_1416264, baseEnd_1416264] using wordTrace_append hprefix tailTrace_1416264
  have hstable : (prefixWord ++ tailWord_1416264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416264).length < 2 ^ (prefixWord ++ tailWord_1416264).sum := by decide
  have hdescent : baseEnd_1416264 < baseStart_1416264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416295 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 5]
def baseStart_1416295 : Nat := 118140960795 + 1416295 * 2 ^ 59
def prefixEnd_1416295 : Nat := 4983230072969 + 3 ^ 40 * 1416295 * 2
def baseEnd_1416295 : Nat := 323217814915396210221815

theorem tailTrace_1416295 : CollatzResearch.WordTrace tailWord_1416295 prefixEnd_1416295 323217814915396210221815 := by
  unfold tailWord_1416295
  simp only [CollatzResearch.WordTrace]
  refine ⟨51656522404012573773746339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34437681602675049182497559 51656522404012573773746339)
  ·
    refine ⟨77484783606018860660619509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51656522404012573773746339 77484783606018860660619509)
    ·
      refine ⟨7264198463064268186933079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77484783606018860660619509 7264198463064268186933079)
      ·
        refine ⟨10896297694596402280399619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7264198463064268186933079 10896297694596402280399619)
        ·
          refine ⟨16344446541894603420599429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10896297694596402280399619 16344446541894603420599429)
          ·
            refine ⟨3064583726605238141362393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16344446541894603420599429 3064583726605238141362393)
            ·
              refine ⟨2298437794953928606021795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064583726605238141362393 2298437794953928606021795)
              ·
                refine ⟨3447656692430892909032693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298437794953928606021795 3447656692430892909032693)
                ·
                  refine ⟨323217814915396210221815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3447656692430892909032693 323217814915396210221815)
                  ·
                    rfl

theorem cell21_1416295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 5].length) (baseStart_1416295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416295 prefixEnd_1416295 := by exact prefixLift 1416295
  have htrace : WordTrace (prefixWord ++ tailWord_1416295) baseStart_1416295 baseEnd_1416295 := by
    simpa [prefixWord, tailWord_1416295, baseEnd_1416295] using wordTrace_append hprefix tailTrace_1416295
  have hstable : (prefixWord ++ tailWord_1416295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416295).length < 2 ^ (prefixWord ++ tailWord_1416295).sum := by decide
  have hdescent : baseEnd_1416295 < baseStart_1416295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416323 : List Nat := [1, 1, 1, 3, 3, 2, 3, 7]
def baseStart_1416323 : Nat := 118140960795 + 1416323 * 2 ^ 59
def prefixEnd_1416323 : Nat := 4983230072969 + 3 ^ 40 * 1416323 * 2
def baseEnd_1416323 : Nat := 107741401632291461251697

theorem tailTrace_1416323 : CollatzResearch.WordTrace tailWord_1416323 prefixEnd_1416323 107741401632291461251697 := by
  unfold tailWord_1416323
  simp only [CollatzResearch.WordTrace]
  refine ⟨51657543647911134555765623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34438362431940756370510415 51657543647911134555765623)
  ·
    refine ⟨77486315471866701833648435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51657543647911134555765623 77486315471866701833648435)
    ·
      refine ⟨116229473207800052750472653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77486315471866701833648435 116229473207800052750472653)
      ·
        refine ⟨43586052452925019781427245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116229473207800052750472653 43586052452925019781427245)
        ·
          refine ⟨16344769669846882418035217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43586052452925019781427245 16344769669846882418035217)
          ·
            refine ⟨12258577252385161813526413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16344769669846882418035217 12258577252385161813526413)
            ·
              refine ⟨4596966469644435680072405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12258577252385161813526413 4596966469644435680072405)
              ·
                refine ⟨107741401632291461251697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4596966469644435680072405 107741401632291461251697)
                ·
                  rfl

theorem cell21_1416323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 7].length) (baseStart_1416323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416323 prefixEnd_1416323 := by exact prefixLift 1416323
  have htrace : WordTrace (prefixWord ++ tailWord_1416323) baseStart_1416323 baseEnd_1416323 := by
    simpa [prefixWord, tailWord_1416323, baseEnd_1416323] using wordTrace_append hprefix tailTrace_1416323
  have hstable : (prefixWord ++ tailWord_1416323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416323).length < 2 ^ (prefixWord ++ tailWord_1416323).sum := by decide
  have hdescent : baseEnd_1416323 < baseStart_1416323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416402 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1416402 : Nat := 118140960795 + 1416402 * 2 ^ 59
def prefixEnd_1416402 : Nat := 4983230072969 + 3 ^ 40 * 1416402 * 2
def baseEnd_1416402 : Nat := 323242233773187801938263

theorem tailTrace_1416402 : CollatzResearch.WordTrace tailWord_1416402 prefixEnd_1416402 323242233773187801938263 := by
  unfold tailWord_1416402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915106253656232761972865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34440283343083287365260973 12915106253656232761972865)
  ·
    refine ⟨9686329690242174571479649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12915106253656232761972865 9686329690242174571479649)
    ·
      refine ⟨7264747267681630928609737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9686329690242174571479649 7264747267681630928609737)
      ·
        refine ⟨5448560450761223196457303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7264747267681630928609737 5448560450761223196457303)
        ·
          refine ⟨8172840676141834794685955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5448560450761223196457303 8172840676141834794685955)
          ·
            refine ⟨12259261014212752192028933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8172840676141834794685955 12259261014212752192028933)
            ·
              refine ⟨2298611440164891036005425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12259261014212752192028933 2298611440164891036005425)
              ·
                refine ⟨1723958580123668277004069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2298611440164891036005425 1723958580123668277004069)
                ·
                  refine ⟨323242233773187801938263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1723958580123668277004069 323242233773187801938263)
                  ·
                    rfl

theorem cell21_1416402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1416402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416402 prefixEnd_1416402 := by exact prefixLift 1416402
  have htrace : WordTrace (prefixWord ++ tailWord_1416402) baseStart_1416402 baseEnd_1416402 := by
    simpa [prefixWord, tailWord_1416402, baseEnd_1416402] using wordTrace_append hprefix tailTrace_1416402
  have hstable : (prefixWord ++ tailWord_1416402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416402).length < 2 ^ (prefixWord ++ tailWord_1416402).sum := by decide
  have hdescent : baseEnd_1416402 < baseStart_1416402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416405 : List Nat := [1, 3, 2, 4, 1, 1, 4, 2, 3]
def baseStart_1416405 : Nat := 118140960795 + 1416405 * 2 ^ 59
def prefixEnd_1416405 : Nat := 4983230072969 + 3 ^ 40 * 1416405 * 2
def baseEnd_1416405 : Nat := 323242918414060463388257

theorem tailTrace_1416405 : CollatzResearch.WordTrace tailWord_1416405 prefixEnd_1416405 323242918414060463388257 := by
  unfold tailWord_1416405
  simp only [CollatzResearch.WordTrace]
  refine ⟨51660534433614062560250669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34440356289076041706833779 51660534433614062560250669)
  ·
    refine ⟨19372700412605273460094001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51660534433614062560250669 19372700412605273460094001)
    ·
      refine ⟨14529525309453955095070501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19372700412605273460094001 14529525309453955095070501)
      ·
        refine ⟨2724285995522616580325719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14529525309453955095070501 2724285995522616580325719)
        ·
          refine ⟨4086428993283924870488579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724285995522616580325719 4086428993283924870488579)
          ·
            refine ⟨6129643489925887305732869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086428993283924870488579 6129643489925887305732869)
            ·
              refine ⟨1149308154361103869824913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6129643489925887305732869 1149308154361103869824913)
              ·
                refine ⟨861981115770827902368685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149308154361103869824913 861981115770827902368685)
                ·
                  refine ⟨323242918414060463388257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861981115770827902368685 323242918414060463388257)
                  ·
                    rfl

theorem cell21_1416405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_1416405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416405 prefixEnd_1416405 := by exact prefixLift 1416405
  have htrace : WordTrace (prefixWord ++ tailWord_1416405) baseStart_1416405 baseEnd_1416405 := by
    simpa [prefixWord, tailWord_1416405, baseEnd_1416405] using wordTrace_append hprefix tailTrace_1416405
  have hstable : (prefixWord ++ tailWord_1416405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416405).length < 2 ^ (prefixWord ++ tailWord_1416405).sum := by decide
  have hdescent : baseEnd_1416405 < baseStart_1416405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416416 : List Nat := [2, 1, 1, 3, 1, 6, 1, 6]
def baseStart_1416416 : Nat := 118140960795 + 1416416 * 2 ^ 59
def prefixEnd_1416416 : Nat := 4983230072969 + 3 ^ 40 * 1416416 * 2
def baseEnd_1416416 : Nat := 107748476254642296234967

theorem tailTrace_1416416 : CollatzResearch.WordTrace tailWord_1416416 prefixEnd_1416416 107748476254642296234967 := by
  unfold tailWord_1416416
  simp only [CollatzResearch.WordTrace]
  refine ⟨25830467818287105719450551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34440623757716140959267401 25830467818287105719450551)
  ·
    refine ⟨38745701727430658579175827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25830467818287105719450551 38745701727430658579175827)
    ·
      refine ⟨58118552591145987868763741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38745701727430658579175827 58118552591145987868763741)
      ·
        refine ⟨21794457221679745450786403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58118552591145987868763741 21794457221679745450786403)
        ·
          refine ⟨32691685832519618176179605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21794457221679745450786403 32691685832519618176179605)
          ·
            refine ⟨1532422773399357102008419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32691685832519618176179605 1532422773399357102008419)
            ·
              refine ⟨2298634160099035653012629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532422773399357102008419 2298634160099035653012629)
              ·
                refine ⟨107748476254642296234967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2298634160099035653012629 107748476254642296234967)
                ·
                  rfl

theorem cell21_1416416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_1416416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416416 prefixEnd_1416416 := by exact prefixLift 1416416
  have htrace : WordTrace (prefixWord ++ tailWord_1416416) baseStart_1416416 baseEnd_1416416 := by
    simpa [prefixWord, tailWord_1416416, baseEnd_1416416] using wordTrace_append hprefix tailTrace_1416416
  have hstable : (prefixWord ++ tailWord_1416416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416416).length < 2 ^ (prefixWord ++ tailWord_1416416).sum := by decide
  have hdescent : baseEnd_1416416 < baseStart_1416416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416430 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1416430 : Nat := 118140960795 + 1416430 * 2 ^ 59
def prefixEnd_1416430 : Nat := 4983230072969 + 3 ^ 40 * 1416430 * 2
def baseEnd_1416430 : Nat := 323248623754665975471539

theorem tailTrace_1416430 : CollatzResearch.WordTrace tailWord_1416430 prefixEnd_1416430 323248623754665975471539 := by
  unfold tailWord_1416430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6457680782315436478738843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34440964172348994553273829 6457680782315436478738843)
  ·
    refine ⟨9686521173473154718108265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6457680782315436478738843 9686521173473154718108265)
    ·
      refine ⟨7264890880104866038581199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9686521173473154718108265 7264890880104866038581199)
      ·
        refine ⟨10897336320157299057871799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7264890880104866038581199 10897336320157299057871799)
        ·
          refine ⟨16346004480235948586807699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10897336320157299057871799 16346004480235948586807699)
          ·
            refine ⟨24519006720353922880211549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16346004480235948586807699 24519006720353922880211549)
            ·
              refine ⟨9194627520132721080079331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24519006720353922880211549 9194627520132721080079331)
              ·
                refine ⟨13791941280199081620118997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194627520132721080079331 13791941280199081620118997)
                ·
                  refine ⟨323248623754665975471539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13791941280199081620118997 323248623754665975471539)
                  ·
                    rfl

theorem cell21_1416430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1416430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416430 prefixEnd_1416430 := by exact prefixLift 1416430
  have htrace : WordTrace (prefixWord ++ tailWord_1416430) baseStart_1416430 baseEnd_1416430 := by
    simpa [prefixWord, tailWord_1416430, baseEnd_1416430] using wordTrace_append hprefix tailTrace_1416430
  have hstable : (prefixWord ++ tailWord_1416430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416430).length < 2 ^ (prefixWord ++ tailWord_1416430).sum := by decide
  have hdescent : baseEnd_1416430 < baseStart_1416430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416447 : List Nat := [1, 1, 2, 2, 1, 5, 1, 5, 3]
def baseStart_1416447 : Nat := 118140960795 + 1416447 * 2 ^ 59
def prefixEnd_1416447 : Nat := 4983230072969 + 3 ^ 40 * 1416447 * 2
def baseEnd_1416447 : Nat := 323252503386277723688171

theorem tailTrace_1416447 : CollatzResearch.WordTrace tailWord_1416447 prefixEnd_1416447 323252503386277723688171 := by
  unfold tailWord_1416447
  simp only [CollatzResearch.WordTrace]
  refine ⟨51662066299461903733279595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34441377532974602488853063 51662066299461903733279595)
  ·
    refine ⟨77493099449192855599919393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51662066299461903733279595 77493099449192855599919393)
    ·
      refine ⟨58119824586894641699939545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77493099449192855599919393 58119824586894641699939545)
      ·
        refine ⟨43589868440170981274954659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58119824586894641699939545 43589868440170981274954659)
        ·
          refine ⟨65384802660256471912431989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43589868440170981274954659 65384802660256471912431989)
          ·
            refine ⟨6129825249399044241790499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65384802660256471912431989 6129825249399044241790499)
            ·
              refine ⟨9194737874098566362685749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129825249399044241790499 9194737874098566362685749)
              ·
                refine ⟨862006675696740596501789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9194737874098566362685749 862006675696740596501789)
                ·
                  refine ⟨323252503386277723688171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862006675696740596501789 323252503386277723688171)
                  ·
                    rfl

theorem cell21_1416447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 3].length) (baseStart_1416447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416447 prefixEnd_1416447 := by exact prefixLift 1416447
  have htrace : WordTrace (prefixWord ++ tailWord_1416447) baseStart_1416447 baseEnd_1416447 := by
    simpa [prefixWord, tailWord_1416447, baseEnd_1416447] using wordTrace_append hprefix tailTrace_1416447
  have hstable : (prefixWord ++ tailWord_1416447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416447).length < 2 ^ (prefixWord ++ tailWord_1416447).sum := by decide
  have hdescent : baseEnd_1416447 < baseStart_1416447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416489 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 11]
def baseStart_1416489 : Nat := 118140960795 + 1416489 * 2 ^ 59
def prefixEnd_1416489 : Nat := 4983230072969 + 3 ^ 40 * 1416489 * 2
def baseEnd_1416489 : Nat := 323262088358494983988085

theorem tailTrace_1416489 : CollatzResearch.WordTrace tailWord_1416489 prefixEnd_1416489 323262088358494983988085 := by
  unfold tailWord_1416489
  simp only [CollatzResearch.WordTrace]
  refine ⟨51663598165309744906308521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34442398776873163270872347 51663598165309744906308521)
  ·
    refine ⟨38747698623982308679731391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51663598165309744906308521 38747698623982308679731391)
    ·
      refine ⟨58121547935973463019597087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38747698623982308679731391 58121547935973463019597087)
      ·
        refine ⟨87182321903960194529395631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58121547935973463019597087 87182321903960194529395631)
        ·
          refine ⟨130773482855940291794093447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87182321903960194529395631 130773482855940291794093447)
          ·
            refine ⟨196160224283910437691140171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130773482855940291794093447 196160224283910437691140171)
            ·
              refine ⟨294240336425865656536710257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196160224283910437691140171 294240336425865656536710257)
              ·
                refine ⟨220680252319399242402532693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294240336425865656536710257 220680252319399242402532693)
                ·
                  refine ⟨323262088358494983988085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 220680252319399242402532693 323262088358494983988085)
                  ·
                    rfl

theorem cell21_1416489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_1416489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416489 prefixEnd_1416489 := by exact prefixLift 1416489
  have htrace : WordTrace (prefixWord ++ tailWord_1416489) baseStart_1416489 baseEnd_1416489 := by
    simpa [prefixWord, tailWord_1416489, baseEnd_1416489] using wordTrace_append hprefix tailTrace_1416489
  have hstable : (prefixWord ++ tailWord_1416489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416489).length < 2 ^ (prefixWord ++ tailWord_1416489).sum := by decide
  have hdescent : baseEnd_1416489 < baseStart_1416489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416509 : List Nat := [1, 4, 1, 5, 1, 2, 7]
def baseStart_1416509 : Nat := 118140960795 + 1416509 * 2 ^ 59
def prefixEnd_1416509 : Nat := 4983230072969 + 3 ^ 40 * 1416509 * 2
def baseEnd_1416509 : Nat := 35918516958997710406079

theorem tailTrace_1416509 : CollatzResearch.WordTrace tailWord_1416509 prefixEnd_1416509 35918516958997710406079 := by
  unfold tailWord_1416509
  simp only [CollatzResearch.WordTrace]
  refine ⟨51664327625237288322036581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34442885083491525548024387 51664327625237288322036581)
  ·
    refine ⟨9687061429731991560381859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51664327625237288322036581 9687061429731991560381859)
    ·
      refine ⟨14530592144597987340572789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9687061429731991560381859 14530592144597987340572789)
      ·
        refine ⟨1362243013556061313178699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14530592144597987340572789 1362243013556061313178699)
        ·
          refine ⟨2043364520334091969768049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362243013556061313178699 2043364520334091969768049)
          ·
            refine ⟨1532523390250568977326037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2043364520334091969768049 1532523390250568977326037)
            ·
              refine ⟨35918516958997710406079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1532523390250568977326037 35918516958997710406079)
              ·
                rfl

theorem cell21_1416509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 7].length) (baseStart_1416509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416509 prefixEnd_1416509 := by exact prefixLift 1416509
  have htrace : WordTrace (prefixWord ++ tailWord_1416509) baseStart_1416509 baseEnd_1416509 := by
    simpa [prefixWord, tailWord_1416509, baseEnd_1416509] using wordTrace_append hprefix tailTrace_1416509
  have hstable : (prefixWord ++ tailWord_1416509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416509).length < 2 ^ (prefixWord ++ tailWord_1416509).sum := by decide
  have hdescent : baseEnd_1416509 < baseStart_1416509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416574 : List Nat := [4, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_1416574 : Nat := 118140960795 + 1416574 * 2 ^ 59
def prefixEnd_1416574 : Nat := 4983230072969 + 3 ^ 40 * 1416574 * 2
def baseEnd_1416574 : Nat := 323281486516553725071245

theorem tailTrace_1416574 : CollatzResearch.WordTrace tailWord_1416574 prefixEnd_1416574 323281486516553725071245 := by
  unfold tailWord_1416574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6458337296250225552894097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34444465580001202948768517 6458337296250225552894097)
  ·
    refine ⟨4843752972187669164670573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6458337296250225552894097 4843752972187669164670573)
    ·
      refine ⟨1816407364570375936751465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4843752972187669164670573 1816407364570375936751465)
      ·
        refine ⟨1362305523427781952563599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1816407364570375936751465 1362305523427781952563599)
        ·
          refine ⟨2043458285141672928845399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362305523427781952563599 2043458285141672928845399)
          ·
            refine ⟨3065187427712509393268099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043458285141672928845399 3065187427712509393268099)
            ·
              refine ⟨4597781141568764089902149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3065187427712509393268099 4597781141568764089902149)
              ·
                refine ⟨862083964044143266856653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4597781141568764089902149 862083964044143266856653)
                ·
                  refine ⟨323281486516553725071245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862083964044143266856653 323281486516553725071245)
                  ·
                    rfl

theorem cell21_1416574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_1416574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416574 prefixEnd_1416574 := by exact prefixLift 1416574
  have htrace : WordTrace (prefixWord ++ tailWord_1416574) baseStart_1416574 baseEnd_1416574 := by
    simpa [prefixWord, tailWord_1416574, baseEnd_1416574] using wordTrace_append hprefix tailTrace_1416574
  have hstable : (prefixWord ++ tailWord_1416574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416574).length < 2 ^ (prefixWord ++ tailWord_1416574).sum := by decide
  have hdescent : baseEnd_1416574 < baseStart_1416574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416585 : List Nat := [1, 2, 1, 1, 8, 1, 1, 6]
def baseStart_1416585 : Nat := 118140960795 + 1416585 * 2 ^ 59
def prefixEnd_1416585 : Nat := 4983230072969 + 3 ^ 40 * 1416585 * 2
def baseEnd_1416585 : Nat := 107761332288806716795963

theorem tailTrace_1416585 : CollatzResearch.WordTrace tailWord_1416585 prefixEnd_1416585 107761332288806716795963 := by
  unfold tailWord_1416585
  simp only [CollatzResearch.WordTrace]
  refine ⟨51667099572961953301803209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34444733048641302201202139 51667099572961953301803209)
  ·
    refine ⟨38750324679721464976352407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51667099572961953301803209 38750324679721464976352407)
    ·
      refine ⟨58125487019582197464528611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38750324679721464976352407 58125487019582197464528611)
      ·
        refine ⟨87188230529373296196792917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58125487019582197464528611 87188230529373296196792917)
        ·
          refine ⟨1021737076516093314806167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 87188230529373296196792917 1021737076516093314806167)
          ·
            refine ⟨1532605614774139972209251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021737076516093314806167 1532605614774139972209251)
            ·
              refine ⟨2298908422161209958313877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532605614774139972209251 2298908422161209958313877)
              ·
                refine ⟨107761332288806716795963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2298908422161209958313877 107761332288806716795963)
                ·
                  rfl

theorem cell21_1416585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 6].length) (baseStart_1416585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416585 prefixEnd_1416585 := by exact prefixLift 1416585
  have htrace : WordTrace (prefixWord ++ tailWord_1416585) baseStart_1416585 baseEnd_1416585 := by
    simpa [prefixWord, tailWord_1416585, baseEnd_1416585] using wordTrace_append hprefix tailTrace_1416585
  have hstable : (prefixWord ++ tailWord_1416585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416585).length < 2 ^ (prefixWord ++ tailWord_1416585).sum := by decide
  have hdescent : baseEnd_1416585 < baseStart_1416585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416810 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_1416810 : Nat := 118140960795 + 1416810 * 2 ^ 59
def prefixEnd_1416810 : Nat := 4983230072969 + 3 ^ 40 * 1416810 * 2
def baseEnd_1416810 : Nat := 323335344931869759137429

theorem tailTrace_1416810 : CollatzResearch.WordTrace tailWord_1416810 prefixEnd_1416810 323335344931869759137429 := by
  unfold tailWord_1416810
  simp only [CollatzResearch.WordTrace]
  refine ⟨12918826499286704182185971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34450203998097877819162589 12918826499286704182185971)
  ·
    refine ⟨19378239748930056273278957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12918826499286704182185971 19378239748930056273278957)
    ·
      refine ⟨7266839905848771102479609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19378239748930056273278957 7266839905848771102479609)
      ·
        refine ⟨5450129929386578326859707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7266839905848771102479609 5450129929386578326859707)
        ·
          refine ⟨8175194894079867490289561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5450129929386578326859707 8175194894079867490289561)
          ·
            refine ⟨6131396170559900617717171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8175194894079867490289561 6131396170559900617717171)
            ·
              refine ⟨9197094255839850926575757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131396170559900617717171 9197094255839850926575757)
              ·
                refine ⟨3448910345939944097465909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9197094255839850926575757 3448910345939944097465909)
                ·
                  refine ⟨323335344931869759137429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3448910345939944097465909 323335344931869759137429)
                  ·
                    rfl

theorem cell21_1416810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_1416810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416810 prefixEnd_1416810 := by exact prefixLift 1416810
  have htrace : WordTrace (prefixWord ++ tailWord_1416810) baseStart_1416810 baseEnd_1416810 := by
    simpa [prefixWord, tailWord_1416810, baseEnd_1416810] using wordTrace_append hprefix tailTrace_1416810
  have hstable : (prefixWord ++ tailWord_1416810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416810).length < 2 ^ (prefixWord ++ tailWord_1416810).sum := by decide
  have hdescent : baseEnd_1416810 < baseStart_1416810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416855 : List Nat := [1, 1, 3, 3, 2, 4, 7]
def baseStart_1416855 : Nat := 118140960795 + 1416855 * 2 ^ 59
def prefixEnd_1416855 : Nat := 4983230072969 + 3 ^ 40 * 1416855 * 2
def baseEnd_1416855 : Nat := 35927290504995520098593

theorem tailTrace_1416855 : CollatzResearch.WordTrace tailWord_1416855 prefixEnd_1416855 35927290504995520098593 := by
  unfold tailWord_1416855
  simp only [CollatzResearch.WordTrace]
  refine ⟨51676947281983789414132019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34451298187989192942754679 51676947281983789414132019)
  ·
    refine ⟨77515420922975684121198029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51676947281983789414132019 77515420922975684121198029)
    ·
      refine ⟨29068282846115881545449261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77515420922975684121198029 29068282846115881545449261)
      ·
        refine ⟨10900606067293455579543473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29068282846115881545449261 10900606067293455579543473)
        ·
          refine ⟨8175454550470091684657605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10900606067293455579543473 8175454550470091684657605)
          ·
            refine ⟨1532897728213142190873301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8175454550470091684657605 1532897728213142190873301)
            ·
              refine ⟨35927290504995520098593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1532897728213142190873301 35927290504995520098593)
              ·
                rfl

theorem cell21_1416855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 7].length) (baseStart_1416855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416855 prefixEnd_1416855 := by exact prefixLift 1416855
  have htrace : WordTrace (prefixWord ++ tailWord_1416855) baseStart_1416855 baseEnd_1416855 := by
    simpa [prefixWord, tailWord_1416855, baseEnd_1416855] using wordTrace_append hprefix tailTrace_1416855
  have hstable : (prefixWord ++ tailWord_1416855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416855).length < 2 ^ (prefixWord ++ tailWord_1416855).sum := by decide
  have hdescent : baseEnd_1416855 < baseStart_1416855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416945 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 7]
def baseStart_1416945 : Nat := 118140960795 + 1416945 * 2 ^ 59
def prefixEnd_1416945 : Nat := 4983230072969 + 3 ^ 40 * 1416945 * 2
def baseEnd_1416945 : Nat := 323366153771139524387153

theorem tailTrace_1416945 : CollatzResearch.WordTrace tailWord_1416945 prefixEnd_1416945 323366153771139524387153 := by
  unfold tailWord_1416945
  simp only [CollatzResearch.WordTrace]
  refine ⟨51680229851657734784908289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34453486567771823189938859 51680229851657734784908289)
  ·
    refine ⟨38760172388743301088681217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51680229851657734784908289 38760172388743301088681217)
    ·
      refine ⟨29070129291557475816510913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38760172388743301088681217 29070129291557475816510913)
      ·
        refine ⟨21802596968668106862383185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29070129291557475816510913 21802596968668106862383185)
        ·
          refine ⟨16351947726501080146787389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21802596968668106862383185 16351947726501080146787389)
          ·
            refine ⟨6131980397437905055045271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16351947726501080146787389 6131980397437905055045271)
            ·
              refine ⟨9197970596156857582567907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131980397437905055045271 9197970596156857582567907)
              ·
                refine ⟨13796955894235286373851861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197970596156857582567907 13796955894235286373851861)
                ·
                  refine ⟨323366153771139524387153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13796955894235286373851861 323366153771139524387153)
                  ·
                    rfl

theorem cell21_1416945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_1416945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416945 prefixEnd_1416945 := by exact prefixLift 1416945
  have htrace : WordTrace (prefixWord ++ tailWord_1416945) baseStart_1416945 baseEnd_1416945 := by
    simpa [prefixWord, tailWord_1416945, baseEnd_1416945] using wordTrace_append hprefix tailTrace_1416945
  have hstable : (prefixWord ++ tailWord_1416945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416945).length < 2 ^ (prefixWord ++ tailWord_1416945).sum := by decide
  have hdescent : baseEnd_1416945 < baseStart_1416945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416962 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1416962 : Nat := 118140960795 + 1416962 * 2 ^ 59
def prefixEnd_1416962 : Nat := 4983230072969 + 3 ^ 40 * 1416962 * 2
def baseEnd_1416962 : Nat := 323370033402751272603785

theorem tailTrace_1416962 : CollatzResearch.WordTrace tailWord_1416962 prefixEnd_1416962 323370033402751272603785 := by
  unfold tailWord_1416962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12920212473149036672069285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34453899928397431125518093 12920212473149036672069285)
  ·
    refine ⟨2422539838715444376012991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12920212473149036672069285 2422539838715444376012991)
    ·
      refine ⟨3633809758073166564019487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2422539838715444376012991 3633809758073166564019487)
      ·
        refine ⟨5450714637109749846029231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3633809758073166564019487 5450714637109749846029231)
        ·
          refine ⟨8176071955664624769043847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5450714637109749846029231 8176071955664624769043847)
          ·
            refine ⟨12264107933496937153565771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8176071955664624769043847 12264107933496937153565771)
            ·
              refine ⟨18396161900245405730348657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12264107933496937153565771 18396161900245405730348657)
              ·
                refine ⟨13797121425184054297761493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18396161900245405730348657 13797121425184054297761493)
                ·
                  refine ⟨323370033402751272603785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13797121425184054297761493 323370033402751272603785)
                  ·
                    rfl

theorem cell21_1416962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1416962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1416962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1416962 prefixEnd_1416962 := by exact prefixLift 1416962
  have htrace : WordTrace (prefixWord ++ tailWord_1416962) baseStart_1416962 baseEnd_1416962 := by
    simpa [prefixWord, tailWord_1416962, baseEnd_1416962] using wordTrace_append hprefix tailTrace_1416962
  have hstable : (prefixWord ++ tailWord_1416962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416962).length < 2 ^ (prefixWord ++ tailWord_1416962).sum := by decide
  have hdescent : baseEnd_1416962 < baseStart_1416962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417013 : List Nat := [1, 3, 3, 1, 5, 1, 1, 3, 3]
def baseStart_1417013 : Nat := 118140960795 + 1417013 * 2 ^ 59
def prefixEnd_1417013 : Nat := 4983230072969 + 3 ^ 40 * 1417013 * 2
def baseEnd_1417013 : Nat := 323381672297586517253681

theorem tailTrace_1417013 : CollatzResearch.WordTrace tailWord_1417013 prefixEnd_1417013 323381672297586517253681 := by
  unfold tailWord_1417013
  simp only [CollatzResearch.WordTrace]
  refine ⟨51682710015411382398383693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34455140010274254932255795 51682710015411382398383693)
  ·
    refine ⟨19381016255779268399393885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51682710015411382398383693 19381016255779268399393885)
    ·
      refine ⟨7267881095917225649772707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19381016255779268399393885 7267881095917225649772707)
      ·
        refine ⟨10901821643875838474659061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7267881095917225649772707 10901821643875838474659061)
        ·
          refine ⟨1022045779113359856999287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10901821643875838474659061 1022045779113359856999287)
          ·
            refine ⟨1533068668670039785498931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022045779113359856999287 1533068668670039785498931)
            ·
              refine ⟨2299603003005059678248397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533068668670039785498931 2299603003005059678248397)
              ·
                refine ⟨862351126126897379343149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2299603003005059678248397 862351126126897379343149)
                ·
                  refine ⟨323381672297586517253681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862351126126897379343149 323381672297586517253681)
                  ·
                    rfl

theorem cell21_1417013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_1417013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417013 prefixEnd_1417013 := by exact prefixLift 1417013
  have htrace : WordTrace (prefixWord ++ tailWord_1417013) baseStart_1417013 baseEnd_1417013 := by
    simpa [prefixWord, tailWord_1417013, baseEnd_1417013] using wordTrace_append hprefix tailTrace_1417013
  have hstable : (prefixWord ++ tailWord_1417013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417013).length < 2 ^ (prefixWord ++ tailWord_1417013).sum := by decide
  have hdescent : baseEnd_1417013 < baseStart_1417013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417030 : List Nat := [6, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1417030 : Nat := 118140960795 + 1417030 * 2 ^ 59
def prefixEnd_1417030 : Nat := 4983230072969 + 3 ^ 40 * 1417030 * 2
def baseEnd_1417030 : Nat := 323385551929198265470313

theorem tailTrace_1417030 : CollatzResearch.WordTrace tailWord_1417030 prefixEnd_1417030 323385551929198265470313 := by
  unfold tailWord_1417030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615104064260931071929767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34455553370899862867835029 1615104064260931071929767)
  ·
    refine ⟨2422656096391396607894651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1615104064260931071929767 2422656096391396607894651)
    ·
      refine ⟨3633984144587094911841977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2422656096391396607894651 3633984144587094911841977)
      ·
        refine ⟨2725488108440321183881483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3633984144587094911841977 2725488108440321183881483)
        ·
          refine ⟨4088232162660481775822225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725488108440321183881483 4088232162660481775822225)
          ·
            refine ⟨3066174121995361331866669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4088232162660481775822225 3066174121995361331866669)
            ·
              refine ⟨1149815295748260499450001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3066174121995361331866669 1149815295748260499450001)
              ·
                refine ⟨862361471811195374587501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149815295748260499450001 862361471811195374587501)
                ·
                  refine ⟨323385551929198265470313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862361471811195374587501 323385551929198265470313)
                  ·
                    rfl

theorem cell21_1417030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1417030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417030 prefixEnd_1417030 := by exact prefixLift 1417030
  have htrace : WordTrace (prefixWord ++ tailWord_1417030) baseStart_1417030 baseEnd_1417030 := by
    simpa [prefixWord, tailWord_1417030, baseEnd_1417030] using wordTrace_append hprefix tailTrace_1417030
  have hstable : (prefixWord ++ tailWord_1417030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417030).length < 2 ^ (prefixWord ++ tailWord_1417030).sum := by decide
  have hdescent : baseEnd_1417030 < baseStart_1417030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417086 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1417086 : Nat := 118140960795 + 1417086 * 2 ^ 59
def prefixEnd_1417086 : Nat := 4983230072969 + 3 ^ 40 * 1417086 * 2
def baseEnd_1417086 : Nat := 323398331892154612536865

theorem tailTrace_1417086 : CollatzResearch.WordTrace tailWord_1417086 prefixEnd_1417086 323398331892154612536865 := by
  unfold tailWord_1417086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6460671568018364483223889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34456915029431277243860741 6460671568018364483223889)
  ·
    refine ⟨4845503676013773362417917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6460671568018364483223889 4845503676013773362417917)
    ·
      refine ⟨1817063878505165010906719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4845503676013773362417917 1817063878505165010906719)
      ·
        refine ⟨2725595817757747516360079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817063878505165010906719 2725595817757747516360079)
        ·
          refine ⟨4088393726636621274540119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725595817757747516360079 4088393726636621274540119)
          ·
            refine ⟨6132590589954931911810179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4088393726636621274540119 6132590589954931911810179)
            ·
              refine ⟨9198885884932397867715269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132590589954931911810179 9198885884932397867715269)
              ·
                refine ⟨1724791103424824600196613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9198885884932397867715269 1724791103424824600196613)
                ·
                  refine ⟨323398331892154612536865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1724791103424824600196613 323398331892154612536865)
                  ·
                    rfl

theorem cell21_1417086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1417086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417086 prefixEnd_1417086 := by exact prefixLift 1417086
  have htrace : WordTrace (prefixWord ++ tailWord_1417086) baseStart_1417086 baseEnd_1417086 := by
    simpa [prefixWord, tailWord_1417086, baseEnd_1417086] using wordTrace_append hprefix tailTrace_1417086
  have hstable : (prefixWord ++ tailWord_1417086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417086).length < 2 ^ (prefixWord ++ tailWord_1417086).sum := by decide
  have hdescent : baseEnd_1417086 < baseStart_1417086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417097 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 5]
def baseStart_1417097 : Nat := 118140960795 + 1417097 * 2 ^ 59
def prefixEnd_1417097 : Nat := 4983230072969 + 3 ^ 40 * 1417097 * 2
def baseEnd_1417097 : Nat := 323400842242021037853509

theorem tailTrace_1417097 : CollatzResearch.WordTrace tailWord_1417097 prefixEnd_1417097 323400842242021037853509 := by
  unfold tailWord_1417097
  simp only [CollatzResearch.WordTrace]
  refine ⟨51685773747107064744441545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34457182498071376496294363 51685773747107064744441545)
  ·
    refine ⟨38764330310330298558331159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51685773747107064744441545 38764330310330298558331159)
    ·
      refine ⟨58146495465495447837496739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38764330310330298558331159 58146495465495447837496739)
      ·
        refine ⟨87219743198243171756245109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58146495465495447837496739 87219743198243171756245109)
        ·
          refine ⟨8176850924835297352147979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87219743198243171756245109 8176850924835297352147979)
          ·
            refine ⟨12265276387252946028221969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8176850924835297352147979 12265276387252946028221969)
            ·
              refine ⟨9198957290439709521166477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12265276387252946028221969 9198957290439709521166477)
              ·
                refine ⟨3449608983914891070437429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9198957290439709521166477 3449608983914891070437429)
                ·
                  refine ⟨323400842242021037853509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3449608983914891070437429 323400842242021037853509)
                  ·
                    rfl

theorem cell21_1417097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_1417097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417097 prefixEnd_1417097 := by exact prefixLift 1417097
  have htrace : WordTrace (prefixWord ++ tailWord_1417097) baseStart_1417097 baseEnd_1417097 := by
    simpa [prefixWord, tailWord_1417097, baseEnd_1417097] using wordTrace_append hprefix tailTrace_1417097
  have hstable : (prefixWord ++ tailWord_1417097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417097).length < 2 ^ (prefixWord ++ tailWord_1417097).sum := by decide
  have hdescent : baseEnd_1417097 < baseStart_1417097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417114 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1417114 : Nat := 118140960795 + 1417114 * 2 ^ 59
def prefixEnd_1417114 : Nat := 4983230072969 + 3 ^ 40 * 1417114 * 2
def baseEnd_1417114 : Nat := 323404721873632786070141

theorem tailTrace_1417114 : CollatzResearch.WordTrace tailWord_1417114 prefixEnd_1417114 323404721873632786070141 := by
  unfold tailWord_1417114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921598447011369161952599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34457595858696984431873597 12921598447011369161952599)
  ·
    refine ⟨19382397670517053742928899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12921598447011369161952599 19382397670517053742928899)
    ·
      refine ⟨29073596505775580614393349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19382397670517053742928899 29073596505775580614393349)
      ·
        refine ⟨5451299344832921365198753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29073596505775580614393349 5451299344832921365198753)
        ·
          refine ⟨4088474508624691023899065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5451299344832921365198753 4088474508624691023899065)
          ·
            refine ⟨3066355881468518267924299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4088474508624691023899065 3066355881468518267924299)
            ·
              refine ⟨4599533822202777401886449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066355881468518267924299 4599533822202777401886449)
              ·
                refine ⟨3449650366652083051414837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4599533822202777401886449 3449650366652083051414837)
                ·
                  refine ⟨323404721873632786070141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3449650366652083051414837 323404721873632786070141)
                  ·
                    rfl

theorem cell21_1417114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1417114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417114 prefixEnd_1417114 := by exact prefixLift 1417114
  have htrace : WordTrace (prefixWord ++ tailWord_1417114) baseStart_1417114 baseEnd_1417114 := by
    simpa [prefixWord, tailWord_1417114, baseEnd_1417114] using wordTrace_append hprefix tailTrace_1417114
  have hstable : (prefixWord ++ tailWord_1417114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417114).length < 2 ^ (prefixWord ++ tailWord_1417114).sum := by decide
  have hdescent : baseEnd_1417114 < baseStart_1417114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417221 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 4]
def baseStart_1417221 : Nat := 118140960795 + 1417221 * 2 ^ 59
def prefixEnd_1417221 : Nat := 4983230072969 + 3 ^ 40 * 1417221 * 2
def baseEnd_1417221 : Nat := 323429140731424377786589

theorem tailTrace_1417221 : CollatzResearch.WordTrace tailWord_1417221 prefixEnd_1417221 323429140731424377786589 := by
  unfold tailWord_1417221
  simp only [CollatzResearch.WordTrace]
  refine ⟨51690296398657833921955517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34460197599105222614637011 51690296398657833921955517)
  ·
    refine ⟨19383861149496687720733319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51690296398657833921955517 19383861149496687720733319)
    ·
      refine ⟨29075791724245031581099979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19383861149496687720733319 29075791724245031581099979)
      ·
        refine ⟨43613687586367547371649969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29075791724245031581099979 43613687586367547371649969)
        ·
          refine ⟨32710265689775660528737477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43613687586367547371649969 32710265689775660528737477)
          ·
            refine ⟨6133174816832936349138277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32710265689775660528737477 6133174816832936349138277)
            ·
              refine ⟨1149970278156175565463427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6133174816832936349138277 1149970278156175565463427)
              ·
                refine ⟨1724955417234263348195141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149970278156175565463427 1724955417234263348195141)
                ·
                  refine ⟨323429140731424377786589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1724955417234263348195141 323429140731424377786589)
                  ·
                    rfl

theorem cell21_1417221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_1417221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417221 prefixEnd_1417221 := by exact prefixLift 1417221
  have htrace : WordTrace (prefixWord ++ tailWord_1417221) baseStart_1417221 baseEnd_1417221 := by
    simpa [prefixWord, tailWord_1417221, baseEnd_1417221] using wordTrace_append hprefix tailTrace_1417221
  have hstable : (prefixWord ++ tailWord_1417221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417221).length < 2 ^ (prefixWord ++ tailWord_1417221).sum := by decide
  have hdescent : baseEnd_1417221 < baseStart_1417221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417280 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_1417280 : Nat := 118140960795 + 1417280 * 2 ^ 59
def prefixEnd_1417280 : Nat := 4983230072969 + 3 ^ 40 * 1417280 * 2
def baseEnd_1417280 : Nat := 323442605335253386303135

theorem tailTrace_1417280 : CollatzResearch.WordTrace tailWord_1417280 prefixEnd_1417280 323442605335253386303135 := by
  unfold tailWord_1417280
  simp only [CollatzResearch.WordTrace]
  refine ⟨25846224152722043499176647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34461632203629391332235529 25846224152722043499176647)
  ·
    refine ⟨38769336229083065248764971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25846224152722043499176647 38769336229083065248764971)
    ·
      refine ⟨58154004343624597873147457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38769336229083065248764971 58154004343624597873147457)
      ·
        refine ⟨43615503257718448404860593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58154004343624597873147457 43615503257718448404860593)
        ·
          refine ⟨32711627443288836303645445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43615503257718448404860593 32711627443288836303645445)
          ·
            refine ⟨6133430145616656806933521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32711627443288836303645445 6133430145616656806933521)
            ·
              refine ⟨4600072609212492605200141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6133430145616656806933521 4600072609212492605200141)
              ·
                refine ⟨1725027228454684726950053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4600072609212492605200141 1725027228454684726950053)
                ·
                  refine ⟨323442605335253386303135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1725027228454684726950053 323442605335253386303135)
                  ·
                    rfl

theorem cell21_1417280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_1417280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417280 prefixEnd_1417280 := by exact prefixLift 1417280
  have htrace : WordTrace (prefixWord ++ tailWord_1417280) baseStart_1417280 baseEnd_1417280 := by
    simpa [prefixWord, tailWord_1417280, baseEnd_1417280] using wordTrace_append hprefix tailTrace_1417280
  have hstable : (prefixWord ++ tailWord_1417280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417280).length < 2 ^ (prefixWord ++ tailWord_1417280).sum := by decide
  have hdescent : baseEnd_1417280 < baseStart_1417280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417345 : List Nat := [1, 2, 4, 2, 4, 1, 2, 5]
def baseStart_1417345 : Nat := 118140960795 + 1417345 * 2 ^ 59
def prefixEnd_1417345 : Nat := 4983230072969 + 3 ^ 40 * 1417345 * 2
def baseEnd_1417345 : Nat := 107819146406942572573223

theorem tailTrace_1417345 : CollatzResearch.WordTrace tailWord_1417345 prefixEnd_1417345 107819146406942572573223 := by
  unfold tailWord_1417345
  simp only [CollatzResearch.WordTrace]
  refine ⟨51694819050208603099469489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34463212700139068732979659 51694819050208603099469489)
  ·
    refine ⟨38771114287656452324602117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51694819050208603099469489 38771114287656452324602117)
    ·
      refine ⟨7269583928935584810862897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38771114287656452324602117 7269583928935584810862897)
      ·
        refine ⟨5452187946701688608147173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7269583928935584810862897 5452187946701688608147173)
        ·
          refine ⟨1022285240006566614027595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5452187946701688608147173 1022285240006566614027595)
          ·
            refine ⟨1533427860009849921041393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022285240006566614027595 1533427860009849921041393)
            ·
              refine ⟨1150070895007387440781045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1533427860009849921041393 1150070895007387440781045)
              ·
                refine ⟨107819146406942572573223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1150070895007387440781045 107819146406942572573223)
                ·
                  rfl

theorem cell21_1417345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 5].length) (baseStart_1417345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417345 prefixEnd_1417345 := by exact prefixLift 1417345
  have htrace : WordTrace (prefixWord ++ tailWord_1417345) baseStart_1417345 baseEnd_1417345 := by
    simpa [prefixWord, tailWord_1417345, baseEnd_1417345] using wordTrace_append hprefix tailTrace_1417345
  have hstable : (prefixWord ++ tailWord_1417345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417345).length < 2 ^ (prefixWord ++ tailWord_1417345).sum := by decide
  have hdescent : baseEnd_1417345 < baseStart_1417345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417418 : List Nat := [3, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_1417418 : Nat := 118140960795 + 1417418 * 2 ^ 59
def prefixEnd_1417418 : Nat := 4983230072969 + 3 ^ 40 * 1417418 * 2
def baseEnd_1417418 : Nat := 323474098815395813002853

theorem tailTrace_1417418 : CollatzResearch.WordTrace tailWord_1417418 prefixEnd_1417418 323474098815395813002853 := by
  unfold tailWord_1417418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12924370394736034141719227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34464987719296091044584605 12924370394736034141719227)
  ·
    refine ⟨19386555592104051212578841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12924370394736034141719227 19386555592104051212578841)
    ·
      refine ⟨14539916694078038409434131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19386555592104051212578841 14539916694078038409434131)
      ·
        refine ⟨21809875041117057614151197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14539916694078038409434131 21809875041117057614151197)
        ·
          refine ⟨8178703140418896605306699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21809875041117057614151197 8178703140418896605306699)
          ·
            refine ⟨12268054710628344907960049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8178703140418896605306699 12268054710628344907960049)
            ·
              refine ⟨9201041032971258680970037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12268054710628344907960049 9201041032971258680970037)
              ·
                refine ⟨862597596841055501340941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9201041032971258680970037 862597596841055501340941)
                ·
                  refine ⟨323474098815395813002853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862597596841055501340941 323474098815395813002853)
                  ·
                    rfl

theorem cell21_1417418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_1417418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417418 prefixEnd_1417418 := by exact prefixLift 1417418
  have htrace : WordTrace (prefixWord ++ tailWord_1417418) baseStart_1417418 baseEnd_1417418 := by
    simpa [prefixWord, tailWord_1417418, baseEnd_1417418] using wordTrace_append hprefix tailTrace_1417418
  have hstable : (prefixWord ++ tailWord_1417418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417418).length < 2 ^ (prefixWord ++ tailWord_1417418).sum := by decide
  have hdescent : baseEnd_1417418 < baseStart_1417418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417432 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_1417432 : Nat := 118140960795 + 1417432 * 2 ^ 59
def prefixEnd_1417432 : Nat := 4983230072969 + 3 ^ 40 * 1417432 * 2
def baseEnd_1417432 : Nat := 323477293806134899769491

theorem tailTrace_1417432 : CollatzResearch.WordTrace tailWord_1417432 prefixEnd_1417432 323477293806134899769491 := by
  unfold tailWord_1417432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25848996100446708478943275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34465328133928944638591033 25848996100446708478943275)
  ·
    refine ⟨38773494150670062718414913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25848996100446708478943275 38773494150670062718414913)
    ·
      refine ⟨29080120613002547038811185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38773494150670062718414913 29080120613002547038811185)
      ·
        refine ⟨21810090459751910279108389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29080120613002547038811185 21810090459751910279108389)
        ·
          refine ⟨4089391961203483177332823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21810090459751910279108389 4089391961203483177332823)
          ·
            refine ⟨6134087941805224765999235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089391961203483177332823 6134087941805224765999235)
            ·
              refine ⟨9201131912707837148998853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6134087941805224765999235 9201131912707837148998853)
              ·
                refine ⟨1725212233632719465437285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9201131912707837148998853 1725212233632719465437285)
                ·
                  refine ⟨323477293806134899769491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1725212233632719465437285 323477293806134899769491)
                  ·
                    rfl

theorem cell21_1417432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_1417432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417432 prefixEnd_1417432 := by exact prefixLift 1417432
  have htrace : WordTrace (prefixWord ++ tailWord_1417432) baseStart_1417432 baseEnd_1417432 := by
    simpa [prefixWord, tailWord_1417432, baseEnd_1417432] using wordTrace_append hprefix tailTrace_1417432
  have hstable : (prefixWord ++ tailWord_1417432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417432).length < 2 ^ (prefixWord ++ tailWord_1417432).sum := by decide
  have hdescent : baseEnd_1417432 < baseStart_1417432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417553 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 5]
def baseStart_1417553 : Nat := 118140960795 + 1417553 * 2 ^ 59
def prefixEnd_1417553 : Nat := 4983230072969 + 3 ^ 40 * 1417553 * 2
def baseEnd_1417553 : Nat := 323504907654665578252577

theorem tailTrace_1417553 : CollatzResearch.WordTrace tailWord_1417553 prefixEnd_1417553 323504907654665578252577 := by
  unfold tailWord_1417553
  simp only [CollatzResearch.WordTrace]
  refine ⟨51702405433455054623041313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34468270288970036415360875 51702405433455054623041313)
  ·
    refine ⟨38776804075091290967280985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51702405433455054623041313 38776804075091290967280985)
    ·
      refine ⟨29082603056318468225460739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38776804075091290967280985 29082603056318468225460739)
      ·
        refine ⟨43623904584477702338191109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29082603056318468225460739 43623904584477702338191109)
        ·
          refine ⟨8179482109589569188410833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43623904584477702338191109 8179482109589569188410833)
          ·
            refine ⟨6134611582192176891308125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8179482109589569188410833 6134611582192176891308125)
            ·
              refine ⟨2300479343322066334240547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6134611582192176891308125 2300479343322066334240547)
              ·
                refine ⟨3450719014983099501360821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2300479343322066334240547 3450719014983099501360821)
                ·
                  refine ⟨323504907654665578252577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3450719014983099501360821 323504907654665578252577)
                  ·
                    rfl

theorem cell21_1417553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_1417553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417553 prefixEnd_1417553 := by exact prefixLift 1417553
  have htrace : WordTrace (prefixWord ++ tailWord_1417553) baseStart_1417553 baseEnd_1417553 := by
    simpa [prefixWord, tailWord_1417553, baseEnd_1417553] using wordTrace_append hprefix tailTrace_1417553
  have hstable : (prefixWord ++ tailWord_1417553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417553).length < 2 ^ (prefixWord ++ tailWord_1417553).sum := by decide
  have hdescent : baseEnd_1417553 < baseStart_1417553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417598 : List Nat := [4, 2, 3, 12]
def baseStart_1417598 : Nat := 118140960795 + 1417598 * 2 ^ 59
def prefixEnd_1417598 : Nat := 4983230072969 + 3 ^ 40 * 1417598 * 2
def baseEnd_1417598 : Nat := 1331338178056606995895

theorem tailTrace_1417598 : CollatzResearch.WordTrace tailWord_1417598 prefixEnd_1417598 1331338178056606995895 := by
  unfold tailWord_1417598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463005839786503413553681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34469364478861351538952965 6463005839786503413553681)
  ·
    refine ⟨4847254379839877560165261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6463005839786503413553681 4847254379839877560165261)
    ·
      refine ⟨1817720392439954085061973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4847254379839877560165261 1817720392439954085061973)
      ·
        refine ⟨1331338178056606995895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1817720392439954085061973 1331338178056606995895)
        ·
          rfl

theorem cell21_1417598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 12].length) (baseStart_1417598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417598 prefixEnd_1417598 := by exact prefixLift 1417598
  have htrace : WordTrace (prefixWord ++ tailWord_1417598) baseStart_1417598 baseEnd_1417598 := by
    simpa [prefixWord, tailWord_1417598, baseEnd_1417598] using wordTrace_append hprefix tailTrace_1417598
  have hstable : (prefixWord ++ tailWord_1417598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417598).length < 2 ^ (prefixWord ++ tailWord_1417598).sum := by decide
  have hdescent : baseEnd_1417598 < baseStart_1417598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417601 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 4]
def baseStart_1417601 : Nat := 118140960795 + 1417601 * 2 ^ 59
def prefixEnd_1417601 : Nat := 4983230072969 + 3 ^ 40 * 1417601 * 2
def baseEnd_1417601 : Nat := 323515861908628161452479

theorem tailTrace_1417601 : CollatzResearch.WordTrace tailWord_1417601 prefixEnd_1417601 323515861908628161452479 := by
  unfold tailWord_1417601
  simp only [CollatzResearch.WordTrace]
  refine ⟨51704156137281158820788657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34469437424854105880525771 51704156137281158820788657)
  ·
    refine ⟨38778117102960869115591493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51704156137281158820788657 38778117102960869115591493)
    ·
      refine ⟨7270896956805162959173405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38778117102960869115591493 7270896956805162959173405)
      ·
        refine ⟨2726586358801936109690027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7270896956805162959173405 2726586358801936109690027)
        ·
          refine ⟨4089879538202904164535041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726586358801936109690027 4089879538202904164535041)
          ·
            refine ⟨3067409653652178123401281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4089879538202904164535041 3067409653652178123401281)
            ·
              refine ⟨2300557240239133592550961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3067409653652178123401281 2300557240239133592550961)
              ·
                refine ⟨1725417930179350194413221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300557240239133592550961 1725417930179350194413221)
                ·
                  refine ⟨323515861908628161452479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1725417930179350194413221 323515861908628161452479)
                  ·
                    rfl

theorem cell21_1417601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_1417601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417601 prefixEnd_1417601 := by exact prefixLift 1417601
  have htrace : WordTrace (prefixWord ++ tailWord_1417601) baseStart_1417601 baseEnd_1417601 := by
    simpa [prefixWord, tailWord_1417601, baseEnd_1417601] using wordTrace_append hprefix tailTrace_1417601
  have hstable : (prefixWord ++ tailWord_1417601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417601).length < 2 ^ (prefixWord ++ tailWord_1417601).sum := by decide
  have hdescent : baseEnd_1417601 < baseStart_1417601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417652 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1417652 : Nat := 118140960795 + 1417652 * 2 ^ 59
def prefixEnd_1417652 : Nat := 4983230072969 + 3 ^ 40 * 1417652 * 2
def baseEnd_1417652 : Nat := 323527500803463406102375

theorem tailTrace_1417652 : CollatzResearch.WordTrace tailWord_1417652 prefixEnd_1417652 323527500803463406102375 := by
  unfold tailWord_1417652
  simp only [CollatzResearch.WordTrace]
  refine ⟨25853008130048197265447605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34470677506730929687263473 25853008130048197265447605)
  ·
    refine ⟨2423719512192018493635713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25853008130048197265447605 2423719512192018493635713)
    ·
      refine ⟨1817789634144013870226785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2423719512192018493635713 1817789634144013870226785)
      ·
        refine ⟨1363342225608010402670089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1817789634144013870226785 1363342225608010402670089)
        ·
          refine ⟨1022506669206007802002567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1363342225608010402670089 1022506669206007802002567)
          ·
            refine ⟨1533760003809011703003851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022506669206007802002567 1533760003809011703003851)
            ·
              refine ⟨2300640005713517554505777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533760003809011703003851 2300640005713517554505777)
              ·
                refine ⟨1725480004285138165879333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300640005713517554505777 1725480004285138165879333)
                ·
                  refine ⟨323527500803463406102375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1725480004285138165879333 323527500803463406102375)
                  ·
                    rfl

theorem cell21_1417652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1417652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417652 prefixEnd_1417652 := by exact prefixLift 1417652
  have htrace : WordTrace (prefixWord ++ tailWord_1417652) baseStart_1417652 baseEnd_1417652 := by
    simpa [prefixWord, tailWord_1417652, baseEnd_1417652] using wordTrace_append hprefix tailTrace_1417652
  have hstable : (prefixWord ++ tailWord_1417652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417652).length < 2 ^ (prefixWord ++ tailWord_1417652).sum := by decide
  have hdescent : baseEnd_1417652 < baseStart_1417652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417660 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_1417660 : Nat := 118140960795 + 1417660 * 2 ^ 59
def prefixEnd_1417660 : Nat := 4983230072969 + 3 ^ 40 * 1417660 * 2
def baseEnd_1417660 : Nat := 323529326512457169969025

theorem tailTrace_1417660 : CollatzResearch.WordTrace tailWord_1417660 prefixEnd_1417660 323529326512457169969025 := by
  unfold tailWord_1417660
  simp only [CollatzResearch.WordTrace]
  refine ⟨25853154022033705948593217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34470872029378274598124289 25853154022033705948593217)
  ·
    refine ⟨19389865516525279461444913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25853154022033705948593217 19389865516525279461444913)
    ·
      refine ⟨14542399137393959596083685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19389865516525279461444913 14542399137393959596083685)
      ·
        refine ⟨2726699838261367424265691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14542399137393959596083685 2726699838261367424265691)
        ·
          refine ⟨4090049757392051136398537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726699838261367424265691 4090049757392051136398537)
          ·
            refine ⟨3067537318044038352298903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4090049757392051136398537 3067537318044038352298903)
            ·
              refine ⟨4601305977066057528448355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3067537318044038352298903 4601305977066057528448355)
              ·
                refine ⟨6901958965599086292672533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4601305977066057528448355 6901958965599086292672533)
                ·
                  refine ⟨323529326512457169969025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6901958965599086292672533 323529326512457169969025)
                  ·
                    rfl

theorem cell21_1417660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_1417660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417660 prefixEnd_1417660 := by exact prefixLift 1417660
  have htrace : WordTrace (prefixWord ++ tailWord_1417660) baseStart_1417660 baseEnd_1417660 := by
    simpa [prefixWord, tailWord_1417660, baseEnd_1417660] using wordTrace_append hprefix tailTrace_1417660
  have hstable : (prefixWord ++ tailWord_1417660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417660).length < 2 ^ (prefixWord ++ tailWord_1417660).sum := by decide
  have hdescent : baseEnd_1417660 < baseStart_1417660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417705 : List Nat := [1, 2, 1, 1, 1, 2, 1, 9, 3]
def baseStart_1417705 : Nat := 118140960795 + 1417705 * 2 ^ 59
def prefixEnd_1417705 : Nat := 4983230072969 + 3 ^ 40 * 1417705 * 2
def baseEnd_1417705 : Nat := 323539596125547091718933

theorem tailTrace_1417705 : CollatzResearch.WordTrace tailWord_1417705 prefixEnd_1417705 323539596125547091718933 := by
  unfold tailWord_1417705
  simp only [CollatzResearch.WordTrace]
  refine ⟨51707949328904384582574569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34471966219269589721716379 51707949328904384582574569)
  ·
    refine ⟨38780961996678288436930927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51707949328904384582574569 38780961996678288436930927)
    ·
      refine ⟨58171442995017432655396391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38780961996678288436930927 58171442995017432655396391)
      ·
        refine ⟨87257164492526148983094587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58171442995017432655396391 87257164492526148983094587)
        ·
          refine ⟨130885746738789223474641881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87257164492526148983094587 130885746738789223474641881)
          ·
            refine ⟨98164310054091917605981411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130885746738789223474641881 98164310054091917605981411)
            ·
              refine ⟨147246465081137876408972117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98164310054091917605981411 147246465081137876408972117)
              ·
                refine ⟨862772256334792244583821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 147246465081137876408972117 862772256334792244583821)
                ·
                  refine ⟨323539596125547091718933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862772256334792244583821 323539596125547091718933)
                  ·
                    rfl

theorem cell21_1417705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_1417705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417705 prefixEnd_1417705 := by exact prefixLift 1417705
  have htrace : WordTrace (prefixWord ++ tailWord_1417705) baseStart_1417705 baseEnd_1417705 := by
    simpa [prefixWord, tailWord_1417705, baseEnd_1417705] using wordTrace_append hprefix tailTrace_1417705
  have hstable : (prefixWord ++ tailWord_1417705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417705).length < 2 ^ (prefixWord ++ tailWord_1417705).sum := by decide
  have hdescent : baseEnd_1417705 < baseStart_1417705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417733 : List Nat := [1, 3, 1, 1, 2, 2, 3, 8]
def baseStart_1417733 : Nat := 118140960795 + 1417733 * 2 ^ 59
def prefixEnd_1417733 : Nat := 4983230072969 + 3 ^ 40 * 1417733 * 2
def baseEnd_1417733 : Nat := 107848662035675088417403

theorem tailTrace_1417733 : CollatzResearch.WordTrace tailWord_1417733 prefixEnd_1417733 107848662035675088417403 := by
  unfold tailWord_1417733
  simp only [CollatzResearch.WordTrace]
  refine ⟨51708970572802945364593853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34472647048535296909729235 51708970572802945364593853)
  ·
    refine ⟨19390863964801104511722695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51708970572802945364593853 19390863964801104511722695)
    ·
      refine ⟨29086295947201656767584043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19390863964801104511722695 29086295947201656767584043)
      ·
        refine ⟨43629443920802485151376065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29086295947201656767584043 43629443920802485151376065)
        ·
          refine ⟨32722082940601863863532049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43629443920802485151376065 32722082940601863863532049)
          ·
            refine ⟨24541562205451397897649037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32722082940601863863532049 24541562205451397897649037)
            ·
              refine ⟨9203085827044274211618389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24541562205451397897649037 9203085827044274211618389)
              ·
                refine ⟨107848662035675088417403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9203085827044274211618389 107848662035675088417403)
                ·
                  rfl

theorem cell21_1417733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 8].length) (baseStart_1417733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417733 prefixEnd_1417733 := by exact prefixLift 1417733
  have htrace : WordTrace (prefixWord ++ tailWord_1417733) baseStart_1417733 baseEnd_1417733 := by
    simpa [prefixWord, tailWord_1417733, baseEnd_1417733] using wordTrace_append hprefix tailTrace_1417733
  have hstable : (prefixWord ++ tailWord_1417733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417733).length < 2 ^ (prefixWord ++ tailWord_1417733).sum := by decide
  have hdescent : baseEnd_1417733 < baseStart_1417733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417767 : List Nat := [1, 1, 7, 2, 1, 9]
def baseStart_1417767 : Nat := 118140960795 + 1417767 * 2 ^ 59
def prefixEnd_1417767 : Nat := 4983230072969 + 3 ^ 40 * 1417767 * 2
def baseEnd_1417767 : Nat := 11983472050749954136499

theorem tailTrace_1417767 : CollatzResearch.WordTrace tailWord_1417767 prefixEnd_1417767 11983472050749954136499 := by
  unfold tailWord_1417767
  simp only [CollatzResearch.WordTrace]
  refine ⟨51710210654679769171331555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34473473769786512780887703 51710210654679769171331555)
  ·
    refine ⟨77565315982019653756997333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51710210654679769171331555 77565315982019653756997333)
    ·
      refine ⟨1817937093328585634929625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 77565315982019653756997333 1817937093328585634929625)
      ·
        refine ⟨1363452819996439226197219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1817937093328585634929625 1363452819996439226197219)
        ·
          refine ⟨2045179229994658839295829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363452819996439226197219 2045179229994658839295829)
          ·
            refine ⟨11983472050749954136499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2045179229994658839295829 11983472050749954136499)
            ·
              rfl

theorem cell21_1417767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 9].length) (baseStart_1417767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417767 prefixEnd_1417767 := by exact prefixLift 1417767
  have htrace : WordTrace (prefixWord ++ tailWord_1417767) baseStart_1417767 baseEnd_1417767 := by
    simpa [prefixWord, tailWord_1417767, baseEnd_1417767] using wordTrace_append hprefix tailTrace_1417767
  have hstable : (prefixWord ++ tailWord_1417767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417767).length < 2 ^ (prefixWord ++ tailWord_1417767).sum := by decide
  have hdescent : baseEnd_1417767 < baseStart_1417767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417773 : List Nat := [1, 5, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1417773 : Nat := 118140960795 + 1417773 * 2 ^ 59
def prefixEnd_1417773 : Nat := 4983230072969 + 3 ^ 40 * 1417773 * 2
def baseEnd_1417773 : Nat := 323555114651994084585461

theorem tailTrace_1417773 : CollatzResearch.WordTrace tailWord_1417773 prefixEnd_1417773 323555114651994084585461 := by
  unfold tailWord_1417773
  simp only [CollatzResearch.WordTrace]
  refine ⟨51710429492658032196049973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34473619661772021464033315 51710429492658032196049973)
  ·
    refine ⟨4847852764936690518379685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51710429492658032196049973 4847852764936690518379685)
    ·
      refine ⟨908972393425629472196191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4847852764936690518379685 908972393425629472196191)
      ·
        refine ⟨1363458590138444208294287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908972393425629472196191 1363458590138444208294287)
        ·
          refine ⟨2045187885207666312441431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363458590138444208294287 2045187885207666312441431)
          ·
            refine ⟨3067781827811499468662147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045187885207666312441431 3067781827811499468662147)
            ·
              refine ⟨4601672741717249202993221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3067781827811499468662147 4601672741717249202993221)
              ·
                refine ⟨862813639071984225561229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4601672741717249202993221 862813639071984225561229)
                ·
                  refine ⟨323555114651994084585461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862813639071984225561229 323555114651994084585461)
                  ·
                    rfl

theorem cell21_1417773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1417773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417773 prefixEnd_1417773 := by exact prefixLift 1417773
  have htrace : WordTrace (prefixWord ++ tailWord_1417773) baseStart_1417773 baseEnd_1417773 := by
    simpa [prefixWord, tailWord_1417773, baseEnd_1417773] using wordTrace_append hprefix tailTrace_1417773
  have hstable : (prefixWord ++ tailWord_1417773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417773).length < 2 ^ (prefixWord ++ tailWord_1417773).sum := by decide
  have hdescent : baseEnd_1417773 < baseStart_1417773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417798 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1417798 : Nat := 118140960795 + 1417798 * 2 ^ 59
def prefixEnd_1417798 : Nat := 4983230072969 + 3 ^ 40 * 1417798 * 2
def baseEnd_1417798 : Nat := 323560819992599596668743

theorem tailTrace_1417798 : CollatzResearch.WordTrace tailWord_1417798 prefixEnd_1417798 323560819992599596668743 := by
  unfold tailWord_1417798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615979416173983170803439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34474227545044974310473365 1615979416173983170803439)
  ·
    refine ⟨2423969124260974756205159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1615979416173983170803439 2423969124260974756205159)
    ·
      refine ⟨3635953686391462134307739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2423969124260974756205159 3635953686391462134307739)
      ·
        refine ⟨5453930529587193201461609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635953686391462134307739 5453930529587193201461609)
        ·
          refine ⟨4090447897190394901096207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5453930529587193201461609 4090447897190394901096207)
          ·
            refine ⟨6135671845785592351644311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4090447897190394901096207 6135671845785592351644311)
            ·
              refine ⟨9203507768678388527466467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6135671845785592351644311 9203507768678388527466467)
              ·
                refine ⟨13805261653017582791199701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9203507768678388527466467 13805261653017582791199701)
                ·
                  refine ⟨323560819992599596668743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13805261653017582791199701 323560819992599596668743)
                  ·
                    rfl

theorem cell21_1417798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1417798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417798 prefixEnd_1417798 := by exact prefixLift 1417798
  have htrace : WordTrace (prefixWord ++ tailWord_1417798) baseStart_1417798 baseEnd_1417798 := by
    simpa [prefixWord, tailWord_1417798, baseEnd_1417798] using wordTrace_append hprefix tailTrace_1417798
  have hstable : (prefixWord ++ tailWord_1417798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417798).length < 2 ^ (prefixWord ++ tailWord_1417798).sum := by decide
  have hdescent : baseEnd_1417798 < baseStart_1417798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417829 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 4]
def baseStart_1417829 : Nat := 118140960795 + 1417829 * 2 ^ 59
def prefixEnd_1417829 : Nat := 4983230072969 + 3 ^ 40 * 1417829 * 2
def baseEnd_1417829 : Nat := 323567894614950431652013

theorem tailTrace_1417829 : CollatzResearch.WordTrace tailWord_1417829 prefixEnd_1417829 323567894614950431652013 := by
  unfold tailWord_1417829
  simp only [CollatzResearch.WordTrace]
  refine ⟨51712471980455153760088541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34474981320303435840059027 51712471980455153760088541)
  ·
    refine ⟨19392176992670682660033203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51712471980455153760088541 19392176992670682660033203)
    ·
      refine ⟨29088265489006023990049805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19392176992670682660033203 29088265489006023990049805)
      ·
        refine ⟨10908099558377258996268677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29088265489006023990049805 10908099558377258996268677)
        ·
          refine ⟨2045268667195736061800377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10908099558377258996268677 2045268667195736061800377)
          ·
            refine ⟨1533951500396802046350283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2045268667195736061800377 1533951500396802046350283)
            ·
              refine ⟨2300927250595203069525425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533951500396802046350283 2300927250595203069525425)
              ·
                refine ⟨1725695437946402302144069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300927250595203069525425 1725695437946402302144069)
                ·
                  refine ⟨323567894614950431652013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1725695437946402302144069 323567894614950431652013)
                  ·
                    rfl

theorem cell21_1417829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_1417829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417829 prefixEnd_1417829 := by exact prefixLift 1417829
  have htrace : WordTrace (prefixWord ++ tailWord_1417829) baseStart_1417829 baseEnd_1417829 := by
    simpa [prefixWord, tailWord_1417829, baseEnd_1417829] using wordTrace_append hprefix tailTrace_1417829
  have hstable : (prefixWord ++ tailWord_1417829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417829).length < 2 ^ (prefixWord ++ tailWord_1417829).sum := by decide
  have hdescent : baseEnd_1417829 < baseStart_1417829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417846 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1417846 : Nat := 118140960795 + 1417846 * 2 ^ 59
def prefixEnd_1417846 : Nat := 4983230072969 + 3 ^ 40 * 1417846 * 2
def baseEnd_1417846 : Nat := 323571774246562179868645

theorem tailTrace_1417846 : CollatzResearch.WordTrace tailWord_1417846 prefixEnd_1417846 323571774246562179868645 := by
  unfold tailWord_1417846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3232068251337097853966087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34475394680929043775638261 3232068251337097853966087)
  ·
    refine ⟨4848102377005646780949131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3232068251337097853966087 4848102377005646780949131)
    ·
      refine ⟨7272153565508470171423697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4848102377005646780949131 7272153565508470171423697)
      ·
        refine ⟨5454115174131352628567773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7272153565508470171423697 5454115174131352628567773)
        ·
          refine ⟨2045293190299257235712915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5454115174131352628567773 2045293190299257235712915)
          ·
            refine ⟨3067939785448885853569373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045293190299257235712915 3067939785448885853569373)
            ·
              refine ⟨1150477419543332195088515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3067939785448885853569373 1150477419543332195088515)
              ·
                refine ⟨1725716129314998292632773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150477419543332195088515 1725716129314998292632773)
                ·
                  refine ⟨323571774246562179868645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1725716129314998292632773 323571774246562179868645)
                  ·
                    rfl

theorem cell21_1417846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1417846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417846 prefixEnd_1417846 := by exact prefixLift 1417846
  have htrace : WordTrace (prefixWord ++ tailWord_1417846) baseStart_1417846 baseEnd_1417846 := by
    simpa [prefixWord, tailWord_1417846, baseEnd_1417846] using wordTrace_append hprefix tailTrace_1417846
  have hstable : (prefixWord ++ tailWord_1417846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417846).length < 2 ^ (prefixWord ++ tailWord_1417846).sum := by decide
  have hdescent : baseEnd_1417846 < baseStart_1417846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417885 : List Nat := [1, 4, 2, 1, 1, 1, 11]
def baseStart_1417885 : Nat := 118140960795 + 1417885 * 2 ^ 59
def prefixEnd_1417885 : Nat := 4983230072969 + 3 ^ 40 * 1417885 * 2
def baseEnd_1417885 : Nat := 35953408286434086524285

theorem tailTrace_1417885 : CollatzResearch.WordTrace tailWord_1417885 prefixEnd_1417885 35953408286434086524285 := by
  unfold tailWord_1417885
  simp only [CollatzResearch.WordTrace]
  refine ⟨51714514468252275324127109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34476342978834850216084739 51714514468252275324127109)
  ·
    refine ⟨9696471462797301623273833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51714514468252275324127109 9696471462797301623273833)
    ·
      refine ⟨7272353597097976217455375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9696471462797301623273833 7272353597097976217455375)
      ·
        refine ⟨10908530395646964326183063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7272353597097976217455375 10908530395646964326183063)
        ·
          refine ⟨16362795593470446489274595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10908530395646964326183063 16362795593470446489274595)
          ·
            refine ⟨24544193390205669733911893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16362795593470446489274595 24544193390205669733911893)
            ·
              refine ⟨35953408286434086524285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24544193390205669733911893 35953408286434086524285)
              ·
                rfl

theorem cell21_1417885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 11].length) (baseStart_1417885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417885 prefixEnd_1417885 := by exact prefixLift 1417885
  have htrace : WordTrace (prefixWord ++ tailWord_1417885) baseStart_1417885 baseEnd_1417885 := by
    simpa [prefixWord, tailWord_1417885, baseEnd_1417885] using wordTrace_append hprefix tailTrace_1417885
  have hstable : (prefixWord ++ tailWord_1417885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417885).length < 2 ^ (prefixWord ++ tailWord_1417885).sum := by decide
  have hdescent : baseEnd_1417885 < baseStart_1417885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417905 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 4]
def baseStart_1417905 : Nat := 118140960795 + 1417905 * 2 ^ 59
def prefixEnd_1417905 : Nat := 4983230072969 + 3 ^ 40 * 1417905 * 2
def baseEnd_1417905 : Nat := 323585238850391188385191

theorem tailTrace_1417905 : CollatzResearch.WordTrace tailWord_1417905 prefixEnd_1417905 323585238850391188385191 := by
  unfold tailWord_1417905
  simp only [CollatzResearch.WordTrace]
  refine ⟨51715243928179818739855169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34476829285453212493236779 51715243928179818739855169)
  ·
    refine ⟨38786432946134864054891377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51715243928179818739855169 38786432946134864054891377)
    ·
      refine ⟨29089824709601148041168533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38786432946134864054891377 29089824709601148041168533)
      ·
        refine ⟨1363585533262553814429775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29089824709601148041168533 1363585533262553814429775)
        ·
          refine ⟨2045378299893830721644663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363585533262553814429775 2045378299893830721644663)
          ·
            refine ⟨3068067449840746082466995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045378299893830721644663 3068067449840746082466995)
            ·
              refine ⟨4602101174761119123700493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068067449840746082466995 4602101174761119123700493)
              ·
                refine ⟨1725787940535419671387685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4602101174761119123700493 1725787940535419671387685)
                ·
                  refine ⟨323585238850391188385191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1725787940535419671387685 323585238850391188385191)
                  ·
                    rfl

theorem cell21_1417905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_1417905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417905 prefixEnd_1417905 := by exact prefixLift 1417905
  have htrace : WordTrace (prefixWord ++ tailWord_1417905) baseStart_1417905 baseEnd_1417905 := by
    simpa [prefixWord, tailWord_1417905, baseEnd_1417905] using wordTrace_append hprefix tailTrace_1417905
  have hstable : (prefixWord ++ tailWord_1417905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417905).length < 2 ^ (prefixWord ++ tailWord_1417905).sum := by decide
  have hdescent : baseEnd_1417905 < baseStart_1417905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417916 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_1417916 : Nat := 118140960795 + 1417916 * 2 ^ 59
def prefixEnd_1417916 : Nat := 4983230072969 + 3 ^ 40 * 1417916 * 2
def baseEnd_1417916 : Nat := 323587749200257613701835

theorem tailTrace_1417916 : CollatzResearch.WordTrace tailWord_1417916 prefixEnd_1417916 323587749200257613701835 := by
  unfold tailWord_1417916
  simp only [CollatzResearch.WordTrace]
  refine ⟨25857822565569983809252801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34477096754093311745670401 25857822565569983809252801)
  ·
    refine ⟨19393366924177487856939601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25857822565569983809252801 19393366924177487856939601)
    ·
      refine ⟨14545025193133115892704701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19393366924177487856939601 14545025193133115892704701)
      ·
        refine ⟨5454384447424918459764263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14545025193133115892704701 5454384447424918459764263)
        ·
          refine ⟨8181576671137377689646395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5454384447424918459764263 8181576671137377689646395)
          ·
            refine ⟨12272365006706066534469593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8181576671137377689646395 12272365006706066534469593)
            ·
              refine ⟨9204273755029549900852195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12272365006706066534469593 9204273755029549900852195)
              ·
                refine ⟨13806410632544324851278293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9204273755029549900852195 13806410632544324851278293)
                ·
                  refine ⟨323587749200257613701835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13806410632544324851278293 323587749200257613701835)
                  ·
                    rfl

theorem cell21_1417916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_1417916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417916 prefixEnd_1417916 := by exact prefixLift 1417916
  have htrace : WordTrace (prefixWord ++ tailWord_1417916) baseStart_1417916 baseEnd_1417916 := by
    simpa [prefixWord, tailWord_1417916, baseEnd_1417916] using wordTrace_append hprefix tailTrace_1417916
  have hstable : (prefixWord ++ tailWord_1417916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417916).length < 2 ^ (prefixWord ++ tailWord_1417916).sum := by decide
  have hdescent : baseEnd_1417916 < baseStart_1417916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417961 : List Nat := [1, 2, 1, 1, 1, 2, 7, 6]
def baseStart_1417961 : Nat := 118140960795 + 1417961 * 2 ^ 59
def prefixEnd_1417961 : Nat := 4983230072969 + 3 ^ 40 * 1417961 * 2
def baseEnd_1417961 : Nat := 107866006271115845150581

theorem tailTrace_1417961 : CollatzResearch.WordTrace tailWord_1417961 prefixEnd_1417961 107866006271115845150581 := by
  unfold tailWord_1417961
  simp only [CollatzResearch.WordTrace]
  refine ⟨51717286415976940303893737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34478190943984626869262491 51717286415976940303893737)
  ·
    refine ⟨38787964811982705227920303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51717286415976940303893737 38787964811982705227920303)
    ·
      refine ⟨58181947217974057841880455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38787964811982705227920303 58181947217974057841880455)
      ·
        refine ⟨87272920826961086762820683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58181947217974057841880455 87272920826961086762820683)
        ·
          refine ⟨130909381240441630144231025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87272920826961086762820683 130909381240441630144231025)
          ·
            refine ⟨98182035930331222608173269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130909381240441630144231025 98182035930331222608173269)
            ·
              refine ⟨2301141467117138029879061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98182035930331222608173269 2301141467117138029879061)
              ·
                refine ⟨107866006271115845150581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2301141467117138029879061 107866006271115845150581)
                ·
                  rfl

theorem cell21_1417961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 6].length) (baseStart_1417961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1417961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1417961 prefixEnd_1417961 := by exact prefixLift 1417961
  have htrace : WordTrace (prefixWord ++ tailWord_1417961) baseStart_1417961 baseEnd_1417961 := by
    simpa [prefixWord, tailWord_1417961, baseEnd_1417961] using wordTrace_append hprefix tailTrace_1417961
  have hstable : (prefixWord ++ tailWord_1417961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417961).length < 2 ^ (prefixWord ++ tailWord_1417961).sum := by decide
  have hdescent : baseEnd_1417961 < baseStart_1417961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418029 : List Nat := [1, 5, 3, 2, 1, 2, 2, 5]
def baseStart_1418029 : Nat := 118140960795 + 1418029 * 2 ^ 59
def prefixEnd_1418029 : Nat := 4983230072969 + 3 ^ 40 * 1418029 * 2
def baseEnd_1418029 : Nat := 107871179113264842772757

theorem tailTrace_1418029 : CollatzResearch.WordTrace tailWord_1418029 prefixEnd_1418029 107871179113264842772757 := by
  unfold tailWord_1418029
  simp only [CollatzResearch.WordTrace]
  refine ⟨51719766579730587917369141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34479844386487058611579427 51719766579730587917369141)
  ·
    refine ⟨4848728116849742617253357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51719766579730587917369141 4848728116849742617253357)
    ·
      refine ⟨1818273043818653481470009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4848728116849742617253357 1818273043818653481470009)
      ·
        refine ⟨1363704782863990111102507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1818273043818653481470009 1363704782863990111102507)
        ·
          refine ⟨2045557174295985166653761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363704782863990111102507 2045557174295985166653761)
          ·
            refine ⟨1534167880721988874990321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2045557174295985166653761 1534167880721988874990321)
            ·
              refine ⟨1150625910541491656242741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534167880721988874990321 1150625910541491656242741)
              ·
                refine ⟨107871179113264842772757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1150625910541491656242741 107871179113264842772757)
                ·
                  rfl

theorem cell21_1418029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 5].length) (baseStart_1418029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418029 prefixEnd_1418029 := by exact prefixLift 1418029
  have htrace : WordTrace (prefixWord ++ tailWord_1418029) baseStart_1418029 baseEnd_1418029 := by
    simpa [prefixWord, tailWord_1418029, baseEnd_1418029] using wordTrace_append hprefix tailTrace_1418029
  have hstable : (prefixWord ++ tailWord_1418029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418029).length < 2 ^ (prefixWord ++ tailWord_1418029).sum := by decide
  have hdescent : baseEnd_1418029 < baseStart_1418029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418119 : List Nat := [1, 1, 4, 2, 3, 3, 2, 2, 3]
def baseStart_1418119 : Nat := 118140960795 + 1418119 * 2 ^ 59
def prefixEnd_1418119 : Nat := 4983230072969 + 3 ^ 40 * 1418119 * 2
def baseEnd_1418119 : Nat := 323634076565974371818087

theorem tailTrace_1418119 : CollatzResearch.WordTrace tailWord_1418119 prefixEnd_1418119 323634076565974371818087 := by
  unfold tailWord_1418119
  simp only [CollatzResearch.WordTrace]
  refine ⟨51723049149404533288145411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34482032766269688858763607 51723049149404533288145411)
  ·
    refine ⟨77584573724106799932218117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51723049149404533288145411 77584573724106799932218117)
    ·
      refine ⟨14547107573270024987290897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77584573724106799932218117 14547107573270024987290897)
      ·
        refine ⟨10910330679952518740468173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14547107573270024987290897 10910330679952518740468173)
        ·
          refine ⟨4091374004982194527675565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10910330679952518740468173 4091374004982194527675565)
          ·
            refine ⟨1534265251868322947878337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4091374004982194527675565 1534265251868322947878337)
            ·
              refine ⟨1150698938901242210908753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534265251868322947878337 1150698938901242210908753)
              ·
                refine ⟨863024204175931658181565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150698938901242210908753 863024204175931658181565)
                ·
                  refine ⟨323634076565974371818087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863024204175931658181565 323634076565974371818087)
                  ·
                    rfl

theorem cell21_1418119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 3].length) (baseStart_1418119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418119 prefixEnd_1418119 := by exact prefixLift 1418119
  have htrace : WordTrace (prefixWord ++ tailWord_1418119) baseStart_1418119 baseEnd_1418119 := by
    simpa [prefixWord, tailWord_1418119, baseEnd_1418119] using wordTrace_append hprefix tailTrace_1418119
  have hstable : (prefixWord ++ tailWord_1418119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418119).length < 2 ^ (prefixWord ++ tailWord_1418119).sum := by decide
  have hdescent : baseEnd_1418119 < baseStart_1418119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418251 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 4]
def baseStart_1418251 : Nat := 118140960795 + 1418251 * 2 ^ 59
def prefixEnd_1418251 : Nat := 4983230072969 + 3 ^ 40 * 1418251 * 2
def baseEnd_1418251 : Nat := 323664200764371475617817

theorem tailTrace_1418251 : CollatzResearch.WordTrace tailWord_1418251 prefixEnd_1418251 323664200764371475617817 := by
  unfold tailWord_1418251
  simp only [CollatzResearch.WordTrace]
  refine ⟨51727863584926319831950607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34485242389950879887967071 51727863584926319831950607)
  ·
    refine ⟨77591795377389479747925911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51727863584926319831950607 77591795377389479747925911)
    ·
      refine ⟨116387693066084219621888867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77591795377389479747925911 116387693066084219621888867)
      ·
        refine ⟨174581539599126329432833301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116387693066084219621888867 174581539599126329432833301)
        ·
          refine ⟨8183509668709046692164061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 174581539599126329432833301 8183509668709046692164061)
          ·
            refine ⟨3068816125765892509561523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8183509668709046692164061 3068816125765892509561523)
            ·
              refine ⟨4603224188648838764342285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068816125765892509561523 4603224188648838764342285)
              ·
                refine ⟨1726209070743314536628357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4603224188648838764342285 1726209070743314536628357)
                ·
                  refine ⟨323664200764371475617817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726209070743314536628357 323664200764371475617817)
                  ·
                    rfl

theorem cell21_1418251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 4].length) (baseStart_1418251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418251 prefixEnd_1418251 := by exact prefixLift 1418251
  have htrace : WordTrace (prefixWord ++ tailWord_1418251) baseStart_1418251 baseEnd_1418251 := by
    simpa [prefixWord, tailWord_1418251, baseEnd_1418251] using wordTrace_append hprefix tailTrace_1418251
  have hstable : (prefixWord ++ tailWord_1418251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418251).length < 2 ^ (prefixWord ++ tailWord_1418251).sum := by decide
  have hdescent : baseEnd_1418251 < baseStart_1418251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418282 : List Nat := [3, 1, 4, 1, 4, 8]
def baseStart_1418282 : Nat := 118140960795 + 1418282 * 2 ^ 59
def prefixEnd_1418282 : Nat := 4983230072969 + 3 ^ 40 * 1418282 * 2
def baseEnd_1418282 : Nat := 11987825014323048540781

theorem tailTrace_1418282 : CollatzResearch.WordTrace tailWord_1418282 prefixEnd_1418282 11987825014323048540781 := by
  unfold tailWord_1418282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12932248561953503031582275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34485996165209341417552733 12932248561953503031582275)
  ·
    refine ⟨19398372842930254547373413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12932248561953503031582275 19398372842930254547373413)
    ·
      refine ⟨3637194908049422727632515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19398372842930254547373413 3637194908049422727632515)
      ·
        refine ⟨5455792362074134091448773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3637194908049422727632515 5455792362074134091448773)
        ·
          refine ⟨1022961067888900142146645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5455792362074134091448773 1022961067888900142146645)
          ·
            refine ⟨11987825014323048540781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1022961067888900142146645 11987825014323048540781)
            ·
              rfl

theorem cell21_1418282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 8].length) (baseStart_1418282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418282 prefixEnd_1418282 := by exact prefixLift 1418282
  have htrace : WordTrace (prefixWord ++ tailWord_1418282) baseStart_1418282 baseEnd_1418282 := by
    simpa [prefixWord, tailWord_1418282, baseEnd_1418282] using wordTrace_append hprefix tailTrace_1418282
  have hstable : (prefixWord ++ tailWord_1418282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418282).length < 2 ^ (prefixWord ++ tailWord_1418282).sum := by decide
  have hdescent : baseEnd_1418282 < baseStart_1418282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418344 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_1418344 : Nat := 118140960795 + 1418344 * 2 ^ 59
def prefixEnd_1418344 : Nat := 4983230072969 + 3 ^ 40 * 1418344 * 2
def baseEnd_1418344 : Nat := 323685424631423980567627

theorem tailTrace_1418344 : CollatzResearch.WordTrace tailWord_1418344 prefixEnd_1418344 323685424631423980567627 := by
  unfold tailWord_1418344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25865627786794698357543043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34487503715726264476724057 25865627786794698357543043)
  ·
    refine ⟨38798441680192047536314565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25865627786794698357543043 38798441680192047536314565)
    ·
      refine ⟨7274707815036008913058981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38798441680192047536314565 7274707815036008913058981)
      ·
        refine ⟨1364007715319251671198559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7274707815036008913058981 1364007715319251671198559)
        ·
          refine ⟨2046011572978877506797839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364007715319251671198559 2046011572978877506797839)
          ·
            refine ⟨3069017359468316260196759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046011572978877506797839 3069017359468316260196759)
            ·
              refine ⟨4603526039202474390295139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069017359468316260196759 4603526039202474390295139)
              ·
                refine ⟨6905289058803711585442709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4603526039202474390295139 6905289058803711585442709)
                ·
                  refine ⟨323685424631423980567627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6905289058803711585442709 323685424631423980567627)
                  ·
                    rfl

theorem cell21_1418344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_1418344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418344 prefixEnd_1418344 := by exact prefixLift 1418344
  have htrace : WordTrace (prefixWord ++ tailWord_1418344) baseStart_1418344 baseEnd_1418344 := by
    simpa [prefixWord, tailWord_1418344, baseEnd_1418344] using wordTrace_append hprefix tailTrace_1418344
  have hstable : (prefixWord ++ tailWord_1418344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418344).length < 2 ^ (prefixWord ++ tailWord_1418344).sum := by decide
  have hdescent : baseEnd_1418344 < baseStart_1418344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418372 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1418372 : Nat := 118140960795 + 1418372 * 2 ^ 59
def prefixEnd_1418372 : Nat := 4983230072969 + 3 ^ 40 * 1418372 * 2
def baseEnd_1418372 : Nat := 323691814612902154100903

theorem tailTrace_1418372 : CollatzResearch.WordTrace tailWord_1418372 prefixEnd_1418372 323691814612902154100903 := by
  unfold tailWord_1418372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25866138408743978748552685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34488184544991971664736913 25866138408743978748552685)
  ·
    refine ⟨9699801903278992030707257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25866138408743978748552685 9699801903278992030707257)
    ·
      refine ⟨7274851427459244023030443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9699801903278992030707257 7274851427459244023030443)
      ·
        refine ⟨10912277141188866034545665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7274851427459244023030443 10912277141188866034545665)
        ·
          refine ⟨8184207855891649525909249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10912277141188866034545665 8184207855891649525909249)
          ·
            refine ⟨6138155891918737144431937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8184207855891649525909249 6138155891918737144431937)
            ·
              refine ⟨4603616918939052858323953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6138155891918737144431937 4603616918939052858323953)
              ·
                refine ⟨3452712689204289643742965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4603616918939052858323953 3452712689204289643742965)
                ·
                  refine ⟨323691814612902154100903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3452712689204289643742965 323691814612902154100903)
                  ·
                    rfl

theorem cell21_1418372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1418372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418372 prefixEnd_1418372 := by exact prefixLift 1418372
  have htrace : WordTrace (prefixWord ++ tailWord_1418372) baseStart_1418372 baseEnd_1418372 := by
    simpa [prefixWord, tailWord_1418372, baseEnd_1418372] using wordTrace_append hprefix tailTrace_1418372
  have hstable : (prefixWord ++ tailWord_1418372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418372).length < 2 ^ (prefixWord ++ tailWord_1418372).sum := by decide
  have hdescent : baseEnd_1418372 < baseStart_1418372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418417 : List Nat := [1, 2, 2, 5, 1, 1, 1, 8]
def baseStart_1418417 : Nat := 118140960795 + 1418417 * 2 ^ 59
def prefixEnd_1418417 : Nat := 4983230072969 + 3 ^ 40 * 1418417 * 2
def baseEnd_1418417 : Nat := 107900694741997358616937

theorem tailTrace_1418417 : CollatzResearch.WordTrace tailWord_1418417 prefixEnd_1418417 107900694741997358616937 := by
  unfold tailWord_1418417
  simp only [CollatzResearch.WordTrace]
  refine ⟨51733918102324930182493505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34489278734883286788329003 51733918102324930182493505)
  ·
    refine ⟨38800438576743697636870129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51733918102324930182493505 38800438576743697636870129)
    ·
      refine ⟨29100328932557773227652597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38800438576743697636870129 29100328932557773227652597)
      ·
        refine ⟨2728155837427291240092431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29100328932557773227652597 2728155837427291240092431)
        ·
          refine ⟨4092233756140936860138647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2728155837427291240092431 4092233756140936860138647)
          ·
            refine ⟨6138350634211405290207971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092233756140936860138647 6138350634211405290207971)
            ·
              refine ⟨9207525951317107935311957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138350634211405290207971 9207525951317107935311957)
              ·
                refine ⟨107900694741997358616937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9207525951317107935311957 107900694741997358616937)
                ·
                  rfl

theorem cell21_1418417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 8].length) (baseStart_1418417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418417 prefixEnd_1418417 := by exact prefixLift 1418417
  have htrace : WordTrace (prefixWord ++ tailWord_1418417) baseStart_1418417 baseEnd_1418417 := by
    simpa [prefixWord, tailWord_1418417, baseEnd_1418417] using wordTrace_append hprefix tailTrace_1418417
  have hstable : (prefixWord ++ tailWord_1418417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418417).length < 2 ^ (prefixWord ++ tailWord_1418417).sum := by decide
  have hdescent : baseEnd_1418417 < baseStart_1418417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418431 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 5]
def baseStart_1418431 : Nat := 118140960795 + 1418431 * 2 ^ 59
def prefixEnd_1418431 : Nat := 4983230072969 + 3 ^ 40 * 1418431 * 2
def baseEnd_1418431 : Nat := 323705279216731162617449

theorem tailTrace_1418431 : CollatzResearch.WordTrace tailWord_1418431 prefixEnd_1418431 323705279216731162617449 := by
  unfold tailWord_1418431
  simp only [CollatzResearch.WordTrace]
  refine ⟨51734428724274210573503147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34489619149516140382335431 51734428724274210573503147)
  ·
    refine ⟨77601643086411315860254721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51734428724274210573503147 77601643086411315860254721)
    ·
      refine ⟨58201232314808486895191041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77601643086411315860254721 58201232314808486895191041)
      ·
        refine ⟨43650924236106365171393281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58201232314808486895191041 43650924236106365171393281)
        ·
          refine ⟨32738193177079773878544961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43650924236106365171393281 32738193177079773878544961)
          ·
            refine ⟨24553644882809830408908721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32738193177079773878544961 24553644882809830408908721)
            ·
              refine ⟨18415233662107372806681541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24553644882809830408908721 18415233662107372806681541)
              ·
                refine ⟨3452856311645132401252789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18415233662107372806681541 3452856311645132401252789)
                ·
                  refine ⟨323705279216731162617449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3452856311645132401252789 323705279216731162617449)
                  ·
                    rfl

theorem cell21_1418431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_1418431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418431 prefixEnd_1418431 := by exact prefixLift 1418431
  have htrace : WordTrace (prefixWord ++ tailWord_1418431) baseStart_1418431 baseEnd_1418431 := by
    simpa [prefixWord, tailWord_1418431, baseEnd_1418431] using wordTrace_append hprefix tailTrace_1418431
  have hstable : (prefixWord ++ tailWord_1418431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418431).length < 2 ^ (prefixWord ++ tailWord_1418431).sum := by decide
  have hdescent : baseEnd_1418431 < baseStart_1418431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418465 : List Nat := [1, 2, 3, 1, 3, 3, 1, 4, 3]
def baseStart_1418465 : Nat := 118140960795 + 1418465 * 2 ^ 59
def prefixEnd_1418465 : Nat := 4983230072969 + 3 ^ 40 * 1418465 * 2
def baseEnd_1418465 : Nat := 323713038479954659050713

theorem tailTrace_1418465 : CollatzResearch.WordTrace tailWord_1418465 prefixEnd_1418465 323713038479954659050713 := by
  unfold tailWord_1418465
  simp only [CollatzResearch.WordTrace]
  refine ⟨51735668806151034380240849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34490445870767356253493899 51735668806151034380240849)
  ·
    refine ⟨38801751604613275785180637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51735668806151034380240849 38801751604613275785180637)
    ·
      refine ⟨14550656851729978419442739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38801751604613275785180637 14550656851729978419442739)
      ·
        refine ⟨21825985277594967629164109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14550656851729978419442739 21825985277594967629164109)
        ·
          refine ⟨8184744479098112860936541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21825985277594967629164109 8184744479098112860936541)
          ·
            refine ⟨3069279179661792322851203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8184744479098112860936541 3069279179661792322851203)
            ·
              refine ⟨4603918769492688484276805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069279179661792322851203 4603918769492688484276805)
              ·
                refine ⟨863234769279879090801901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4603918769492688484276805 863234769279879090801901)
                ·
                  refine ⟨323713038479954659050713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863234769279879090801901 323713038479954659050713)
                  ·
                    rfl

theorem cell21_1418465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_1418465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418465 prefixEnd_1418465 := by exact prefixLift 1418465
  have htrace : WordTrace (prefixWord ++ tailWord_1418465) baseStart_1418465 baseEnd_1418465 := by
    simpa [prefixWord, tailWord_1418465, baseEnd_1418465] using wordTrace_append hprefix tailTrace_1418465
  have hstable : (prefixWord ++ tailWord_1418465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418465).length < 2 ^ (prefixWord ++ tailWord_1418465).sum := by decide
  have hdescent : baseEnd_1418465 < baseStart_1418465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418541 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1418541 : Nat := 118140960795 + 1418541 * 2 ^ 59
def prefixEnd_1418541 : Nat := 4983230072969 + 3 ^ 40 * 1418541 * 2
def baseEnd_1418541 : Nat := 323730382715395415783891

theorem tailTrace_1418541 : CollatzResearch.WordTrace tailWord_1418541 prefixEnd_1418541 323730382715395415783891 := by
  unfold tailWord_1418541
  simp only [CollatzResearch.WordTrace]
  refine ⟨51738440753875699360007477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34492293835917132906671651 51738440753875699360007477)
  ·
    refine ⟨4850478820675846815000701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51738440753875699360007477 4850478820675846815000701)
    ·
      refine ⟨1818929557753442555625263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4850478820675846815000701 1818929557753442555625263)
      ·
        refine ⟨2728394336630163833437895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1818929557753442555625263 2728394336630163833437895)
        ·
          refine ⟨4092591504945245750156843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2728394336630163833437895 4092591504945245750156843)
          ·
            refine ⟨6138887257417868625235265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092591504945245750156843 6138887257417868625235265)
            ·
              refine ⟨4604165443063401468926449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6138887257417868625235265 4604165443063401468926449)
              ·
                refine ⟨3453124082297551101694837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4604165443063401468926449 3453124082297551101694837)
                ·
                  refine ⟨323730382715395415783891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453124082297551101694837 323730382715395415783891)
                  ·
                    rfl

theorem cell21_1418541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1418541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418541 prefixEnd_1418541 := by exact prefixLift 1418541
  have htrace : WordTrace (prefixWord ++ tailWord_1418541) baseStart_1418541 baseEnd_1418541 := by
    simpa [prefixWord, tailWord_1418541, baseEnd_1418541] using wordTrace_append hprefix tailTrace_1418541
  have hstable : (prefixWord ++ tailWord_1418541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418541).length < 2 ^ (prefixWord ++ tailWord_1418541).sum := by decide
  have hdescent : baseEnd_1418541 < baseStart_1418541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418628 : List Nat := [2, 3, 2, 1, 1, 12]
def baseStart_1418628 : Nat := 118140960795 + 1418628 * 2 ^ 59
def prefixEnd_1418628 : Nat := 4983230072969 + 3 ^ 40 * 1418628 * 2
def baseEnd_1418628 : Nat := 11990749529655651771619

theorem tailTrace_1418628 : CollatzResearch.WordTrace tailWord_1418628 prefixEnd_1418628 11990749529655651771619 := by
  unfold tailWord_1418628
  simp only [CollatzResearch.WordTrace]
  refine ⟨25870806952280256609212269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34494409269707008812283025 25870806952280256609212269)
  ·
    refine ⟨9701552607105096228454601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25870806952280256609212269 9701552607105096228454601)
    ·
      refine ⟨7276164455328822171340951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9701552607105096228454601 7276164455328822171340951)
      ·
        refine ⟨10914246682993233257011427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7276164455328822171340951 10914246682993233257011427)
        ·
          refine ⟨16371370024489849885517141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10914246682993233257011427 16371370024489849885517141)
          ·
            refine ⟨11990749529655651771619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16371370024489849885517141 11990749529655651771619)
            ·
              rfl

theorem cell21_1418628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 12].length) (baseStart_1418628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418628 prefixEnd_1418628 := by exact prefixLift 1418628
  have htrace : WordTrace (prefixWord ++ tailWord_1418628) baseStart_1418628 baseEnd_1418628 := by
    simpa [prefixWord, tailWord_1418628, baseEnd_1418628] using wordTrace_append hprefix tailTrace_1418628
  have hstable : (prefixWord ++ tailWord_1418628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418628).length < 2 ^ (prefixWord ++ tailWord_1418628).sum := by decide
  have hdescent : baseEnd_1418628 < baseStart_1418628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418631 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 4]
def baseStart_1418631 : Nat := 118140960795 + 1418631 * 2 ^ 59
def prefixEnd_1418631 : Nat := 4983230072969 + 3 ^ 40 * 1418631 * 2
def baseEnd_1418631 : Nat := 323750921941575259283707

theorem tailTrace_1418631 : CollatzResearch.WordTrace tailWord_1418631 prefixEnd_1418631 323750921941575259283707 := by
  unfold tailWord_1418631
  simp only [CollatzResearch.WordTrace]
  refine ⟨51741723323549644730783747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34494482215699763153855831 51741723323549644730783747)
  ·
    refine ⟨77612584985324467096175621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51741723323549644730783747 77612584985324467096175621)
    ·
      refine ⟨14552359684748337580532929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77612584985324467096175621 14552359684748337580532929)
      ·
        refine ⟨10914269763561253185399697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14552359684748337580532929 10914269763561253185399697)
        ·
          refine ⟨8185702322670939889049773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10914269763561253185399697 8185702322670939889049773)
          ·
            refine ⟨3069638371001602458393665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8185702322670939889049773 3069638371001602458393665)
            ·
              refine ⟨2302228778251201843795249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3069638371001602458393665 2302228778251201843795249)
              ·
                refine ⟨1726671583688401382846437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2302228778251201843795249 1726671583688401382846437)
                ·
                  refine ⟨323750921941575259283707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726671583688401382846437 323750921941575259283707)
                  ·
                    rfl

theorem cell21_1418631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 4].length) (baseStart_1418631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418631 prefixEnd_1418631 := by exact prefixLift 1418631
  have htrace : WordTrace (prefixWord ++ tailWord_1418631) baseStart_1418631 baseEnd_1418631 := by
    simpa [prefixWord, tailWord_1418631, baseEnd_1418631] using wordTrace_append hprefix tailTrace_1418631
  have hstable : (prefixWord ++ tailWord_1418631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418631).length < 2 ^ (prefixWord ++ tailWord_1418631).sum := by decide
  have hdescent : baseEnd_1418631 < baseStart_1418631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418659 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 5]
def baseStart_1418659 : Nat := 118140960795 + 1418659 * 2 ^ 59
def prefixEnd_1418659 : Nat := 4983230072969 + 3 ^ 40 * 1418659 * 2
def baseEnd_1418659 : Nat := 323757311923053432816983

theorem tailTrace_1418659 : CollatzResearch.WordTrace tailWord_1418659 prefixEnd_1418659 323757311923053432816983 := by
  unfold tailWord_1418659
  simp only [CollatzResearch.WordTrace]
  refine ⟨51742744567448205512803031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34495163044965470341868687 51742744567448205512803031)
  ·
    refine ⟨77614116851172308269204547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51742744567448205512803031 77614116851172308269204547)
    ·
      refine ⟨116421175276758462403806821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77614116851172308269204547 116421175276758462403806821)
      ·
        refine ⟨21828970364392211700713779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116421175276758462403806821 21828970364392211700713779)
        ·
          refine ⟨32743455546588317551070669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21828970364392211700713779 32743455546588317551070669)
          ·
            refine ⟨12278795829970619081651501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32743455546588317551070669 12278795829970619081651501)
            ·
              refine ⟨4604548436238982155619313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12278795829970619081651501 4604548436238982155619313)
              ·
                refine ⟨3453411327179236616714485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4604548436238982155619313 3453411327179236616714485)
                ·
                  refine ⟨323757311923053432816983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453411327179236616714485 323757311923053432816983)
                  ·
                    rfl

theorem cell21_1418659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_1418659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418659 prefixEnd_1418659 := by exact prefixLift 1418659
  have htrace : WordTrace (prefixWord ++ tailWord_1418659) baseStart_1418659 baseEnd_1418659 := by
    simpa [prefixWord, tailWord_1418659, baseEnd_1418659] using wordTrace_append hprefix tailTrace_1418659
  have hstable : (prefixWord ++ tailWord_1418659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418659).length < 2 ^ (prefixWord ++ tailWord_1418659).sum := by decide
  have hdescent : baseEnd_1418659 < baseStart_1418659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418721 : List Nat := [1, 2, 3, 1, 2, 3, 4, 5]
def baseStart_1418721 : Nat := 118140960795 + 1418721 * 2 ^ 59
def prefixEnd_1418721 : Nat := 4983230072969 + 3 ^ 40 * 1418721 * 2
def baseEnd_1418721 : Nat := 107923820389251700927841

theorem tailTrace_1418721 : CollatzResearch.WordTrace tailWord_1418721 prefixEnd_1418721 107923820389251700927841 := by
  unfold tailWord_1418721
  simp only [CollatzResearch.WordTrace]
  refine ⟨51745005893223590101560017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34496670595482393401040011 51745005893223590101560017)
  ·
    refine ⟨38808754419917692576170013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51745005893223590101560017 38808754419917692576170013)
    ·
      refine ⟨14553282907469134716063755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38808754419917692576170013 14553282907469134716063755)
      ·
        refine ⟨21829924361203702074095633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553282907469134716063755 21829924361203702074095633)
        ·
          refine ⟨16372443270902776555571725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21829924361203702074095633 16372443270902776555571725)
          ·
            refine ⟨6139666226588541208339397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16372443270902776555571725 6139666226588541208339397)
            ·
              refine ⟨1151187417485351476563637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6139666226588541208339397 1151187417485351476563637)
              ·
                refine ⟨107923820389251700927841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1151187417485351476563637 107923820389251700927841)
                ·
                  rfl

theorem cell21_1418721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 5].length) (baseStart_1418721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418721 prefixEnd_1418721 := by exact prefixLift 1418721
  have htrace : WordTrace (prefixWord ++ tailWord_1418721) baseStart_1418721 baseEnd_1418721 := by
    simpa [prefixWord, tailWord_1418721, baseEnd_1418721] using wordTrace_append hprefix tailTrace_1418721
  have hstable : (prefixWord ++ tailWord_1418721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418721).length < 2 ^ (prefixWord ++ tailWord_1418721).sum := by decide
  have hdescent : baseEnd_1418721 < baseStart_1418721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418758 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1418758 : Nat := 118140960795 + 1418758 * 2 ^ 59
def prefixEnd_1418758 : Nat := 4983230072969 + 3 ^ 40 * 1418758 * 2
def baseEnd_1418758 : Nat := 323779905071851260666781

theorem tailTrace_1418758 : CollatzResearch.WordTrace tailWord_1418758 prefixEnd_1418758 323779905071851260666781 := by
  unfold tailWord_1418758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1617073606065298294395529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34497570262726363613771285 1617073606065298294395529)
  ·
    refine ⟨1212805204548973720796647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1617073606065298294395529 1212805204548973720796647)
    ·
      refine ⟨1819207806823460581194971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1212805204548973720796647 1819207806823460581194971)
      ·
        refine ⟨2728811710235190871792457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1819207806823460581194971 2728811710235190871792457)
        ·
          refine ⟨2046608782676393153844343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2728811710235190871792457 2046608782676393153844343)
          ·
            refine ⟨3069913174014589730766515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046608782676393153844343 3069913174014589730766515)
            ·
              refine ⟨4604869761021884596149773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069913174014589730766515 4604869761021884596149773)
              ·
                refine ⟨1726826160383206723556165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4604869761021884596149773 1726826160383206723556165)
                ·
                  refine ⟨323779905071851260666781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726826160383206723556165 323779905071851260666781)
                  ·
                    rfl

theorem cell21_1418758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1418758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418758 prefixEnd_1418758 := by exact prefixLift 1418758
  have htrace : WordTrace (prefixWord ++ tailWord_1418758) baseStart_1418758 baseEnd_1418758 := by
    simpa [prefixWord, tailWord_1418758, baseEnd_1418758] using wordTrace_append hprefix tailTrace_1418758
  have hstable : (prefixWord ++ tailWord_1418758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418758).length < 2 ^ (prefixWord ++ tailWord_1418758).sum := by decide
  have hdescent : baseEnd_1418758 < baseStart_1418758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418780 : List Nat := [2, 2, 3, 1, 2, 1, 1, 9]
def baseStart_1418780 : Nat := 118140960795 + 1418780 * 2 ^ 59
def prefixEnd_1418780 : Nat := 4983230072969 + 3 ^ 40 * 1418780 * 2
def baseEnd_1418780 : Nat := 107928308590528037100023

theorem tailTrace_1418780 : CollatzResearch.WordTrace tailWord_1418780 prefixEnd_1418780 107928308590528037100023 := by
  unfold tailWord_1418780
  simp only [CollatzResearch.WordTrace]
  refine ⟨25873578900004921588978897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34498105200006562118638529 25873578900004921588978897)
  ·
    refine ⟨19405184175003691191734173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25873578900004921588978897 19405184175003691191734173)
    ·
      refine ⟨7276944065626384196900315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19405184175003691191734173 7276944065626384196900315)
      ·
        refine ⟨10915416098439576295350473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7276944065626384196900315 10915416098439576295350473)
        ·
          refine ⟨8186562073829682221512855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10915416098439576295350473 8186562073829682221512855)
          ·
            refine ⟨12279843110744523332269283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186562073829682221512855 12279843110744523332269283)
            ·
              refine ⟨18419764666116784998403925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12279843110744523332269283 18419764666116784998403925)
              ·
                refine ⟨107928308590528037100023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18419764666116784998403925 107928308590528037100023)
                ·
                  rfl

theorem cell21_1418780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_1418780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418780 prefixEnd_1418780 := by exact prefixLift 1418780
  have htrace : WordTrace (prefixWord ++ tailWord_1418780) baseStart_1418780 baseEnd_1418780 := by
    simpa [prefixWord, tailWord_1418780, baseEnd_1418780] using wordTrace_append hprefix tailTrace_1418780
  have hstable : (prefixWord ++ tailWord_1418780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418780).length < 2 ^ (prefixWord ++ tailWord_1418780).sum := by decide
  have hdescent : baseEnd_1418780 < baseStart_1418780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418797 : List Nat := [1, 5, 4, 11]
def baseStart_1418797 : Nat := 118140960795 + 1418797 * 2 ^ 59
def prefixEnd_1418797 : Nat := 4983230072969 + 3 ^ 40 * 1418797 * 2
def baseEnd_1418797 : Nat := 1332464219766238105007

theorem tailTrace_1418797 : CollatzResearch.WordTrace tailWord_1418797 prefixEnd_1418797 1332464219766238105007 := by
  unfold tailWord_1418797
  simp only [CollatzResearch.WordTrace]
  refine ⟨51747777840948255081326645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34498518560632170054217763 51747777840948255081326645)
  ·
    refine ⟨4851354172588898913874373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51747777840948255081326645 4851354172588898913874373)
    ·
      refine ⟨909628907360418546351445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4851354172588898913874373 909628907360418546351445)
      ·
        refine ⟨1332464219766238105007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 909628907360418546351445 1332464219766238105007)
        ·
          rfl

theorem cell21_1418797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 11].length) (baseStart_1418797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418797 prefixEnd_1418797 := by exact prefixLift 1418797
  have htrace : WordTrace (prefixWord ++ tailWord_1418797) baseStart_1418797 baseEnd_1418797 := by
    simpa [prefixWord, tailWord_1418797, baseEnd_1418797] using wordTrace_append hprefix tailTrace_1418797
  have hstable : (prefixWord ++ tailWord_1418797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418797).length < 2 ^ (prefixWord ++ tailWord_1418797).sum := by decide
  have hdescent : baseEnd_1418797 < baseStart_1418797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418887 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 5]
def baseStart_1418887 : Nat := 118140960795 + 1418887 * 2 ^ 59
def prefixEnd_1418887 : Nat := 4983230072969 + 3 ^ 40 * 1418887 * 2
def baseEnd_1418887 : Nat := 323809344629375703016517

theorem tailTrace_1418887 : CollatzResearch.WordTrace tailWord_1418887 prefixEnd_1418887 323809344629375703016517 := by
  unfold tailWord_1418887
  simp only [CollatzResearch.WordTrace]
  refine ⟨51751060410622200452102915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34500706940414800301401943 51751060410622200452102915)
  ·
    refine ⟨77626590615933300678154373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51751060410622200452102915 77626590615933300678154373)
    ·
      refine ⟨14554985740487493877153945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77626590615933300678154373 14554985740487493877153945)
      ·
        refine ⟨10916239305365620407865459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14554985740487493877153945 10916239305365620407865459)
        ·
          refine ⟨16374358958048430611798189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10916239305365620407865459 16374358958048430611798189)
          ·
            refine ⟨6140384609268161479424321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16374358958048430611798189 6140384609268161479424321)
            ·
              refine ⟨4605288456951121109568241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6140384609268161479424321 4605288456951121109568241)
              ·
                refine ⟨3453966342713340832176181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4605288456951121109568241 3453966342713340832176181)
                ·
                  refine ⟨323809344629375703016517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453966342713340832176181 323809344629375703016517)
                  ·
                    rfl

theorem cell21_1418887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_1418887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418887 prefixEnd_1418887 := by exact prefixLift 1418887
  have htrace : WordTrace (prefixWord ++ tailWord_1418887) baseStart_1418887 baseEnd_1418887 := by
    simpa [prefixWord, tailWord_1418887, baseEnd_1418887] using wordTrace_append hprefix tailTrace_1418887
  have hstable : (prefixWord ++ tailWord_1418887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418887).length < 2 ^ (prefixWord ++ tailWord_1418887).sum := by decide
  have hdescent : baseEnd_1418887 < baseStart_1418887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418890 : List Nat := [3, 1, 2, 3, 2, 3, 2, 5]
def baseStart_1418890 : Nat := 118140960795 + 1418890 * 2 ^ 59
def prefixEnd_1418890 : Nat := 4983230072969 + 3 ^ 40 * 1418890 * 2
def baseEnd_1418890 : Nat := 107936676423416121488837

theorem tailTrace_1418890 : CollatzResearch.WordTrace tailWord_1418890 prefixEnd_1418890 107936676423416121488837 := by
  unfold tailWord_1418890
  simp only [CollatzResearch.WordTrace]
  refine ⟨12937792457402832991115531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34500779886407554642974749 12937792457402832991115531)
  ·
    refine ⟨19406688686104249486673297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12937792457402832991115531 19406688686104249486673297)
    ·
      refine ⟨14555016514578187115004973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19406688686104249486673297 14555016514578187115004973)
      ·
        refine ⟨5458131192966820168126865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14555016514578187115004973 5458131192966820168126865)
        ·
          refine ⟨4093598394725115126095149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5458131192966820168126865 4093598394725115126095149)
          ·
            refine ⟨1535099398021918172285681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4093598394725115126095149 1535099398021918172285681)
            ·
              refine ⟨1151324548516438629214261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535099398021918172285681 1151324548516438629214261)
              ·
                refine ⟨107936676423416121488837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1151324548516438629214261 107936676423416121488837)
                ·
                  rfl

theorem cell21_1418890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_1418890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418890 prefixEnd_1418890 := by exact prefixLift 1418890
  have htrace : WordTrace (prefixWord ++ tailWord_1418890) baseStart_1418890 baseEnd_1418890 := by
    simpa [prefixWord, tailWord_1418890, baseEnd_1418890] using wordTrace_append hprefix tailTrace_1418890
  have hstable : (prefixWord ++ tailWord_1418890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418890).length < 2 ^ (prefixWord ++ tailWord_1418890).sum := by decide
  have hdescent : baseEnd_1418890 < baseStart_1418890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418935 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 4]
def baseStart_1418935 : Nat := 118140960795 + 1418935 * 2 ^ 59
def prefixEnd_1418935 : Nat := 4983230072969 + 3 ^ 40 * 1418935 * 2
def baseEnd_1418935 : Nat := 323820298883338286216419

theorem tailTrace_1418935 : CollatzResearch.WordTrace tailWord_1418935 prefixEnd_1418935 323820298883338286216419 := by
  unfold tailWord_1418935
  simp only [CollatzResearch.WordTrace]
  refine ⟨51752811114448304649850259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34501874076298869766566839 51752811114448304649850259)
  ·
    refine ⟨77629216671672456974775389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51752811114448304649850259 77629216671672456974775389)
    ·
      refine ⟨29110956251877171365540771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77629216671672456974775389 29110956251877171365540771)
      ·
        refine ⟨43666434377815757048311157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29110956251877171365540771 43666434377815757048311157)
        ·
          refine ⟨4093728222920227223279171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43666434377815757048311157 4093728222920227223279171)
          ·
            refine ⟨6140592334380340834918757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093728222920227223279171 6140592334380340834918757)
            ·
              refine ⟨1151361062696313906547267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6140592334380340834918757 1151361062696313906547267)
              ·
                refine ⟨1727041594044470859820901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151361062696313906547267 1727041594044470859820901)
                ·
                  refine ⟨323820298883338286216419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727041594044470859820901 323820298883338286216419)
                  ·
                    rfl

theorem cell21_1418935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 4].length) (baseStart_1418935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418935 prefixEnd_1418935 := by exact prefixLift 1418935
  have htrace : WordTrace (prefixWord ++ tailWord_1418935) baseStart_1418935 baseEnd_1418935 := by
    simpa [prefixWord, tailWord_1418935, baseEnd_1418935] using wordTrace_append hprefix tailTrace_1418935
  have hstable : (prefixWord ++ tailWord_1418935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418935).length < 2 ^ (prefixWord ++ tailWord_1418935).sum := by decide
  have hdescent : baseEnd_1418935 < baseStart_1418935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418966 : List Nat := [5, 2, 1, 3, 1, 9]
def baseStart_1418966 : Nat := 118140960795 + 1418966 * 2 ^ 59
def prefixEnd_1418966 : Nat := 4983230072969 + 3 ^ 40 * 1418966 * 2
def baseEnd_1418966 : Nat := 11993606426136634118507

theorem tailTrace_1418966 : CollatzResearch.WordTrace tailWord_1418966 prefixEnd_1418966 11993606426136634118507 := by
  unfold tailWord_1418966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234621361083499809014297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34502627851557331296152501 3234621361083499809014297)
  ·
    refine ⟨2425966020812624856760723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3234621361083499809014297 2425966020812624856760723)
    ·
      refine ⟨3638949031218937285141085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2425966020812624856760723 3638949031218937285141085)
      ·
        refine ⟨1364605886707101481927907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3638949031218937285141085 1364605886707101481927907)
        ·
          refine ⟨2046908830060652222891861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364605886707101481927907 2046908830060652222891861)
          ·
            refine ⟨11993606426136634118507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2046908830060652222891861 11993606426136634118507)
            ·
              rfl

theorem cell21_1418966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 9].length) (baseStart_1418966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418966 prefixEnd_1418966 := by exact prefixLift 1418966
  have htrace : WordTrace (prefixWord ++ tailWord_1418966) baseStart_1418966 baseEnd_1418966 := by
    simpa [prefixWord, tailWord_1418966, baseEnd_1418966] using wordTrace_append hprefix tailTrace_1418966
  have hstable : (prefixWord ++ tailWord_1418966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418966).length < 2 ^ (prefixWord ++ tailWord_1418966).sum := by decide
  have hdescent : baseEnd_1418966 < baseStart_1418966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418972 : List Nat := [2, 2, 5, 1, 3, 1, 2, 2, 3]
def baseStart_1418972 : Nat := 118140960795 + 1418972 * 2 ^ 59
def prefixEnd_1418972 : Nat := 4983230072969 + 3 ^ 40 * 1418972 * 2
def baseEnd_1418972 : Nat := 323828742787434444099677

theorem tailTrace_1418972 : CollatzResearch.WordTrace tailWord_1418972 prefixEnd_1418972 323828742787434444099677 := by
  unfold tailWord_1418972
  simp only [CollatzResearch.WordTrace]
  refine ⟨25877080307657129984473585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34502773743542839979298113 25877080307657129984473585)
  ·
    refine ⟨19407810230742847488355189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25877080307657129984473585 19407810230742847488355189)
    ·
      refine ⟨1819482209132141952033299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19407810230742847488355189 1819482209132141952033299)
      ·
        refine ⟨2729223313698212928049949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1819482209132141952033299 2729223313698212928049949)
        ·
          refine ⟨1023458742636829848018731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2729223313698212928049949 1023458742636829848018731)
          ·
            refine ⟨1535188113955244772028097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023458742636829848018731 1535188113955244772028097)
            ·
              refine ⟨1151391085466433579021073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535188113955244772028097 1151391085466433579021073)
              ·
                refine ⟨863543314099825184265805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151391085466433579021073 863543314099825184265805)
                ·
                  refine ⟨323828742787434444099677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863543314099825184265805 323828742787434444099677)
                  ·
                    rfl

theorem cell21_1418972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_1418972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418972 prefixEnd_1418972 := by exact prefixLift 1418972
  have htrace : WordTrace (prefixWord ++ tailWord_1418972) baseStart_1418972 baseEnd_1418972 := by
    simpa [prefixWord, tailWord_1418972, baseEnd_1418972] using wordTrace_append hprefix tailTrace_1418972
  have hstable : (prefixWord ++ tailWord_1418972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418972).length < 2 ^ (prefixWord ++ tailWord_1418972).sum := by decide
  have hdescent : baseEnd_1418972 < baseStart_1418972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418980 : List Nat := [2, 3, 1, 1, 1, 3, 3, 4, 3]
def baseStart_1418980 : Nat := 118140960795 + 1418980 * 2 ^ 59
def prefixEnd_1418980 : Nat := 4983230072969 + 3 ^ 40 * 1418980 * 2
def baseEnd_1418980 : Nat := 323830568496428207966327

theorem tailTrace_1418980 : CollatzResearch.WordTrace tailWord_1418980 prefixEnd_1418980 323830568496428207966327 := by
  unfold tailWord_1418980
  simp only [CollatzResearch.WordTrace]
  refine ⟨25877226199642638667619197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34502968266190184890158929 25877226199642638667619197)
  ·
    refine ⟨9703959824865989500357199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25877226199642638667619197 9703959824865989500357199)
    ·
      refine ⟨14555939737298984250535799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9703959824865989500357199 14555939737298984250535799)
      ·
        refine ⟨21833909605948476375803699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14555939737298984250535799 21833909605948476375803699)
        ·
          refine ⟨32750864408922714563705549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21833909605948476375803699 32750864408922714563705549)
          ·
            refine ⟨12281574153346017961389581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32750864408922714563705549 12281574153346017961389581)
            ·
              refine ⟨4605590307504756735521093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12281574153346017961389581 4605590307504756735521093)
              ·
                refine ⟨863548182657141887910205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4605590307504756735521093 863548182657141887910205)
                ·
                  refine ⟨323830568496428207966327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863548182657141887910205 323830568496428207966327)
                  ·
                    rfl

theorem cell21_1418980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_1418980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418980 prefixEnd_1418980 := by exact prefixLift 1418980
  have htrace : WordTrace (prefixWord ++ tailWord_1418980) baseStart_1418980 baseEnd_1418980 := by
    simpa [prefixWord, tailWord_1418980, baseEnd_1418980] using wordTrace_append hprefix tailTrace_1418980
  have hstable : (prefixWord ++ tailWord_1418980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418980).length < 2 ^ (prefixWord ++ tailWord_1418980).sum := by decide
  have hdescent : baseEnd_1418980 < baseStart_1418980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418983 : List Nat := [1, 1, 5, 4, 2, 1, 1, 6]
def baseStart_1418983 : Nat := 118140960795 + 1418983 * 2 ^ 59
def prefixEnd_1418983 : Nat := 4983230072969 + 3 ^ 40 * 1418983 * 2
def baseEnd_1418983 : Nat := 107943751045766956472107

theorem tailTrace_1418983 : CollatzResearch.WordTrace tailWord_1418983 prefixEnd_1418983 107943751045766956472107 := by
  unfold tailWord_1418983
  simp only [CollatzResearch.WordTrace]
  refine ⟨51754561818274408847597603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34503041212182939231731735 51754561818274408847597603)
  ·
    refine ⟨77631842727411613271396405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51754561818274408847597603 77631842727411613271396405)
    ·
      refine ⟨7277985255694838744193413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77631842727411613271396405 7277985255694838744193413)
      ·
        refine ⟨1364622235442782264536265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7277985255694838744193413 1364622235442782264536265)
        ·
          refine ⟨1023466676582086698402199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1364622235442782264536265 1023466676582086698402199)
          ·
            refine ⟨1535200014873130047603299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023466676582086698402199 1535200014873130047603299)
            ·
              refine ⟨2302800022309695071404949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535200014873130047603299 2302800022309695071404949)
              ·
                refine ⟨107943751045766956472107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2302800022309695071404949 107943751045766956472107)
                ·
                  rfl

theorem cell21_1418983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 6].length) (baseStart_1418983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418983 prefixEnd_1418983 := by exact prefixLift 1418983
  have htrace : WordTrace (prefixWord ++ tailWord_1418983) baseStart_1418983 baseEnd_1418983 := by
    simpa [prefixWord, tailWord_1418983, baseEnd_1418983] using wordTrace_append hprefix tailTrace_1418983
  have hstable : (prefixWord ++ tailWord_1418983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418983).length < 2 ^ (prefixWord ++ tailWord_1418983).sum := by decide
  have hdescent : baseEnd_1418983 < baseStart_1418983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418994 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1418994 : Nat := 118140960795 + 1418994 * 2 ^ 59
def prefixEnd_1418994 : Nat := 4983230072969 + 3 ^ 40 * 1418994 * 2
def baseEnd_1418994 : Nat := 323833763487167294732965

theorem tailTrace_1418994 : CollatzResearch.WordTrace tailWord_1418994 prefixEnd_1418994 323833763487167294732965 := by
  unfold tailWord_1418994
  simp only [CollatzResearch.WordTrace]
  refine ⟨12938740755308639431562009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34503308680823038484165357 12938740755308639431562009)
  ·
    refine ⟨9704055566481479573671507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12938740755308639431562009 9704055566481479573671507)
    ·
      refine ⟨14556083349722219360507261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9704055566481479573671507 14556083349722219360507261)
      ·
        refine ⟨5458531256145832260190223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14556083349722219360507261 5458531256145832260190223)
        ·
          refine ⟨8187796884218748390285335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458531256145832260190223 8187796884218748390285335)
          ·
            refine ⟨12281695326328122585428003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187796884218748390285335 12281695326328122585428003)
            ·
              refine ⟨18422542989492183878142005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12281695326328122585428003 18422542989492183878142005)
              ·
                refine ⟨1727113405264892238575813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18422542989492183878142005 1727113405264892238575813)
                ·
                  refine ⟨323833763487167294732965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727113405264892238575813 323833763487167294732965)
                  ·
                    rfl

theorem cell21_1418994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1418994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1418994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1418994 prefixEnd_1418994 := by exact prefixLift 1418994
  have htrace : WordTrace (prefixWord ++ tailWord_1418994) baseStart_1418994 baseEnd_1418994 := by
    simpa [prefixWord, tailWord_1418994, baseEnd_1418994] using wordTrace_append hprefix tailTrace_1418994
  have hstable : (prefixWord ++ tailWord_1418994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418994).length < 2 ^ (prefixWord ++ tailWord_1418994).sum := by decide
  have hdescent : baseEnd_1418994 < baseStart_1418994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419039 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 5]
def baseStart_1419039 : Nat := 118140960795 + 1419039 * 2 ^ 59
def prefixEnd_1419039 : Nat := 4983230072969 + 3 ^ 40 * 1419039 * 2
def baseEnd_1419039 : Nat := 323844033100257216482873

theorem tailTrace_1419039 : CollatzResearch.WordTrace tailWord_1419039 prefixEnd_1419039 323844033100257216482873 := by
  unfold tailWord_1419039
  simp only [CollatzResearch.WordTrace]
  refine ⟨51756604306071530411636171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34504402870714353607757447 51756604306071530411636171)
  ·
    refine ⟨77634906459107295617454257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51756604306071530411636171 77634906459107295617454257)
    ·
      refine ⟨58226179844330471713090693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77634906459107295617454257 58226179844330471713090693)
      ·
        refine ⟨10917408720811963446204505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58226179844330471713090693 10917408720811963446204505)
        ·
          refine ⟨8188056540608972584653379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10917408720811963446204505 8188056540608972584653379)
          ·
            refine ⟨12282084810913458876980069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8188056540608972584653379 12282084810913458876980069)
            ·
              refine ⟨2302890902046273539433763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12282084810913458876980069 2302890902046273539433763)
              ·
                refine ⟨3454336353069410309150645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302890902046273539433763 3454336353069410309150645)
                ·
                  refine ⟨323844033100257216482873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3454336353069410309150645 323844033100257216482873)
                  ·
                    rfl

theorem cell21_1419039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 5].length) (baseStart_1419039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419039 prefixEnd_1419039 := by exact prefixLift 1419039
  have htrace : WordTrace (prefixWord ++ tailWord_1419039) baseStart_1419039 baseEnd_1419039 := by
    simpa [prefixWord, tailWord_1419039, baseEnd_1419039] using wordTrace_append hprefix tailTrace_1419039
  have hstable : (prefixWord ++ tailWord_1419039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419039).length < 2 ^ (prefixWord ++ tailWord_1419039).sum := by decide
  have hdescent : baseEnd_1419039 < baseStart_1419039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419070 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1419070 : Nat := 118140960795 + 1419070 * 2 ^ 59
def prefixEnd_1419070 : Nat := 4983230072969 + 3 ^ 40 * 1419070 * 2
def baseEnd_1419070 : Nat := 323851107722608051466143

theorem tailTrace_1419070 : CollatzResearch.WordTrace tailWord_1419070 prefixEnd_1419070 323851107722608051466143 := by
  unfold tailWord_1419070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6469716871119902838251833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34505156645972815137343109 6469716871119902838251833)
  ·
    refine ⟨4852287653339927128688875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6469716871119902838251833 4852287653339927128688875)
    ·
      refine ⟨7278431480009890693033313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4852287653339927128688875 7278431480009890693033313)
      ·
        refine ⟨5458823610007418019774985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7278431480009890693033313 5458823610007418019774985)
        ·
          refine ⟨4094117707505563514831239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5458823610007418019774985 4094117707505563514831239)
          ·
            refine ⟨6141176561258345272246859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094117707505563514831239 6141176561258345272246859)
            ·
              refine ⟨9211764841887517908370289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141176561258345272246859 9211764841887517908370289)
              ·
                refine ⟨6908823631415638431277717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9211764841887517908370289 6908823631415638431277717)
                ·
                  refine ⟨323851107722608051466143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6908823631415638431277717 323851107722608051466143)
                  ·
                    rfl

theorem cell21_1419070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1419070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419070 prefixEnd_1419070 := by exact prefixLift 1419070
  have htrace : WordTrace (prefixWord ++ tailWord_1419070) baseStart_1419070 baseEnd_1419070 := by
    simpa [prefixWord, tailWord_1419070, baseEnd_1419070] using wordTrace_append hprefix tailTrace_1419070
  have hstable : (prefixWord ++ tailWord_1419070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419070).length < 2 ^ (prefixWord ++ tailWord_1419070).sum := by decide
  have hdescent : baseEnd_1419070 < baseStart_1419070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419143 : List Nat := [1, 1, 4, 2, 13]
def baseStart_1419143 : Nat := 118140960795 + 1419143 * 2 ^ 59
def prefixEnd_1419143 : Nat := 4983230072969 + 3 ^ 40 * 1419143 * 2
def baseEnd_1419143 : Nat := 3998367497742915391967

theorem tailTrace_1419143 : CollatzResearch.WordTrace tailWord_1419143 prefixEnd_1419143 3998367497742915391967 := by
  unfold tailWord_1419143
  simp only [CollatzResearch.WordTrace]
  refine ⟨51760397497694756173422083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34506931665129837448948055 51760397497694756173422083)
  ·
    refine ⟨77640596246542134260133125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51760397497694756173422083 77640596246542134260133125)
    ·
      refine ⟨14557611796226650173774961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77640596246542134260133125 14557611796226650173774961)
      ·
        refine ⟨10918208847169987630331221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14557611796226650173774961 10918208847169987630331221)
        ·
          refine ⟨3998367497742915391967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10918208847169987630331221 3998367497742915391967)
          ·
            rfl

theorem cell21_1419143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 13].length) (baseStart_1419143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419143 prefixEnd_1419143 := by exact prefixLift 1419143
  have htrace : WordTrace (prefixWord ++ tailWord_1419143) baseStart_1419143 baseEnd_1419143 := by
    simpa [prefixWord, tailWord_1419143, baseEnd_1419143] using wordTrace_append hprefix tailTrace_1419143
  have hstable : (prefixWord ++ tailWord_1419143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419143).length < 2 ^ (prefixWord ++ tailWord_1419143).sum := by decide
  have hdescent : baseEnd_1419143 < baseStart_1419143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419205 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 4]
def baseStart_1419205 : Nat := 118140960795 + 1419205 * 2 ^ 59
def prefixEnd_1419205 : Nat := 4983230072969 + 3 ^ 40 * 1419205 * 2
def baseEnd_1419205 : Nat := 323881916561877816715867

theorem tailTrace_1419205 : CollatzResearch.WordTrace tailWord_1419205 prefixEnd_1419205 323881916561877816715867 := by
  unfold tailWord_1419205
  simp only [CollatzResearch.WordTrace]
  refine ⟨51762658823470140762179069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34508439215646760508119379 51762658823470140762179069)
  ·
    refine ⟨19410997058801302785817151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51762658823470140762179069 19410997058801302785817151)
    ·
      refine ⟨29116495588201954178725727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19410997058801302785817151 29116495588201954178725727)
      ·
        refine ⟨43674743382302931268088591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29116495588201954178725727 43674743382302931268088591)
        ·
          refine ⟨65512115073454396902132887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43674743382302931268088591 65512115073454396902132887)
          ·
            refine ⟨98268172610181595353199331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65512115073454396902132887 98268172610181595353199331)
            ·
              refine ⟨147402258915272393029798997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98268172610181595353199331 147402258915272393029798997)
              ·
                refine ⟨1727370221663348355817957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 147402258915272393029798997 1727370221663348355817957)
                ·
                  refine ⟨323881916561877816715867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727370221663348355817957 323881916561877816715867)
                  ·
                    rfl

theorem cell21_1419205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_1419205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419205 prefixEnd_1419205 := by exact prefixLift 1419205
  have htrace : WordTrace (prefixWord ++ tailWord_1419205) baseStart_1419205 baseEnd_1419205 := by
    simpa [prefixWord, tailWord_1419205, baseEnd_1419205] using wordTrace_append hprefix tailTrace_1419205
  have hstable : (prefixWord ++ tailWord_1419205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419205).length < 2 ^ (prefixWord ++ tailWord_1419205).sum := by decide
  have hdescent : baseEnd_1419205 < baseStart_1419205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419208 : List Nat := [2, 1, 3, 1, 4, 1, 2, 4, 3]
def baseStart_1419208 : Nat := 118140960795 + 1419208 * 2 ^ 59
def prefixEnd_1419208 : Nat := 4983230072969 + 3 ^ 40 * 1419208 * 2
def baseEnd_1419208 : Nat := 323882601202750478165861

theorem tailTrace_1419208 : CollatzResearch.WordTrace tailWord_1419208 prefixEnd_1419208 323882601202750478165861 := by
  unfold tailWord_1419208
  simp only [CollatzResearch.WordTrace]
  refine ⟨25881384121229636137269139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34508512161639514849692185 25881384121229636137269139)
  ·
    refine ⟨38822076181844454205903709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25881384121229636137269139 38822076181844454205903709)
    ·
      refine ⟨14558278568191670327213891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38822076181844454205903709 14558278568191670327213891)
      ·
        refine ⟨21837417852287505490820837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14558278568191670327213891 21837417852287505490820837)
        ·
          refine ⟨4094515847303907279528907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21837417852287505490820837 4094515847303907279528907)
          ·
            refine ⟨6141773770955860919293361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094515847303907279528907 6141773770955860919293361)
            ·
              refine ⟨4606330328216895689470021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6141773770955860919293361 4606330328216895689470021)
              ·
                refine ⟨863686936540667941775629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4606330328216895689470021 863686936540667941775629)
                ·
                  refine ⟨323882601202750478165861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863686936540667941775629 323882601202750478165861)
                  ·
                    rfl

theorem cell21_1419208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_1419208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419208 prefixEnd_1419208 := by exact prefixLift 1419208
  have htrace : WordTrace (prefixWord ++ tailWord_1419208) baseStart_1419208 baseEnd_1419208 := by
    simpa [prefixWord, tailWord_1419208, baseEnd_1419208] using wordTrace_append hprefix tailTrace_1419208
  have hstable : (prefixWord ++ tailWord_1419208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419208).length < 2 ^ (prefixWord ++ tailWord_1419208).sum := by decide
  have hdescent : baseEnd_1419208 < baseStart_1419208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419228 : List Nat := [2, 2, 6, 1, 1, 2, 2, 5]
def baseStart_1419228 : Nat := 118140960795 + 1419228 * 2 ^ 59
def prefixEnd_1419228 : Nat := 4983230072969 + 3 ^ 40 * 1419228 * 2
def baseEnd_1419228 : Nat := 107962388491744962610829

theorem tailTrace_1419228 : CollatzResearch.WordTrace tailWord_1419228 prefixEnd_1419228 107962388491744962610829 := by
  unfold tailWord_1419228
  simp only [CollatzResearch.WordTrace]
  refine ⟨25881748851193407845133169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34508998468257877126844225 25881748851193407845133169)
  ·
    refine ⟨19411311638395055883849877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25881748851193407845133169 19411311638395055883849877)
    ·
      refine ⟨909905233049768244555463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19411311638395055883849877 909905233049768244555463)
      ·
        refine ⟨1364857849574652366833195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 909905233049768244555463 1364857849574652366833195)
        ·
          refine ⟨2047286774361978550249793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364857849574652366833195 2047286774361978550249793)
          ·
            refine ⟨1535465080771483912687345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2047286774361978550249793 1535465080771483912687345)
            ·
              refine ⟨1151598810578612934515509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535465080771483912687345 1151598810578612934515509)
              ·
                refine ⟨107962388491744962610829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1151598810578612934515509 107962388491744962610829)
                ·
                  rfl

theorem cell21_1419228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_1419228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419228 prefixEnd_1419228 := by exact prefixLift 1419228
  have htrace : WordTrace (prefixWord ++ tailWord_1419228) baseStart_1419228 baseEnd_1419228 := by
    simpa [prefixWord, tailWord_1419228, baseEnd_1419228] using wordTrace_append hprefix tailTrace_1419228
  have hstable : (prefixWord ++ tailWord_1419228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419228).length < 2 ^ (prefixWord ++ tailWord_1419228).sum := by decide
  have hdescent : baseEnd_1419228 < baseStart_1419228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419267 : List Nat := [1, 1, 1, 3, 2, 1, 1, 8, 3]
def baseStart_1419267 : Nat := 118140960795 + 1419267 * 2 ^ 59
def prefixEnd_1419267 : Nat := 4983230072969 + 3 ^ 40 * 1419267 * 2
def baseEnd_1419267 : Nat := 323896065806579486682407

theorem tailTrace_1419267 : CollatzResearch.WordTrace tailWord_1419267 prefixEnd_1419267 323896065806579486682407 := by
  unfold tailWord_1419267
  simp only [CollatzResearch.WordTrace]
  refine ⟨51764920149245525350936055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34509946766163683567290703 51764920149245525350936055)
  ·
    refine ⟨77647380223868288026404083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51764920149245525350936055 77647380223868288026404083)
    ·
      refine ⟨116471070335802432039606125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77647380223868288026404083 116471070335802432039606125)
      ·
        refine ⟨43676651375925912014852297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116471070335802432039606125 43676651375925912014852297)
        ·
          refine ⟨32757488531944434011139223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43676651375925912014852297 32757488531944434011139223)
          ·
            refine ⟨49136232797916651016708835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32757488531944434011139223 49136232797916651016708835)
            ·
              refine ⟨73704349196874976525063253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49136232797916651016708835 73704349196874976525063253)
              ·
                refine ⟨863722842150878631153085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 73704349196874976525063253 863722842150878631153085)
                ·
                  refine ⟨323896065806579486682407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863722842150878631153085 323896065806579486682407)
                  ·
                    rfl

theorem cell21_1419267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 3].length) (baseStart_1419267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419267 prefixEnd_1419267 := by exact prefixLift 1419267
  have htrace : WordTrace (prefixWord ++ tailWord_1419267) baseStart_1419267 baseEnd_1419267 := by
    simpa [prefixWord, tailWord_1419267, baseEnd_1419267] using wordTrace_append hprefix tailTrace_1419267
  have hstable : (prefixWord ++ tailWord_1419267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419267).length < 2 ^ (prefixWord ++ tailWord_1419267).sum := by decide
  have hdescent : baseEnd_1419267 < baseStart_1419267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419295 : List Nat := [1, 1, 2, 4, 1, 2, 1, 9]
def baseStart_1419295 : Nat := 118140960795 + 1419295 * 2 ^ 59
def prefixEnd_1419295 : Nat := 4983230072969 + 3 ^ 40 * 1419295 * 2
def baseEnd_1419295 : Nat := 107967485262685886738561

theorem tailTrace_1419295 : CollatzResearch.WordTrace tailWord_1419295 prefixEnd_1419295 107967485262685886738561 := by
  unfold tailWord_1419295
  simp only [CollatzResearch.WordTrace]
  refine ⟨51765941393144086132955339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34510627595429390755303559 51765941393144086132955339)
  ·
    refine ⟨77648912089716129199433009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51765941393144086132955339 77648912089716129199433009)
    ·
      refine ⟨58236684067287096899574757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77648912089716129199433009 58236684067287096899574757)
      ·
        refine ⟨10919378262616330668670267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58236684067287096899574757 10919378262616330668670267)
        ·
          refine ⟨16379067393924496003005401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10919378262616330668670267 16379067393924496003005401)
          ·
            refine ⟨12284300545443372002254051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16379067393924496003005401 12284300545443372002254051)
            ·
              refine ⟨18426450818165058003381077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12284300545443372002254051 18426450818165058003381077)
              ·
                refine ⟨107967485262685886738561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18426450818165058003381077 107967485262685886738561)
                ·
                  rfl

theorem cell21_1419295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 9].length) (baseStart_1419295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419295 prefixEnd_1419295 := by exact prefixLift 1419295
  have htrace : WordTrace (prefixWord ++ tailWord_1419295) baseStart_1419295 baseEnd_1419295 := by
    simpa [prefixWord, tailWord_1419295, baseEnd_1419295] using wordTrace_append hprefix tailTrace_1419295
  have hstable : (prefixWord ++ tailWord_1419295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419295).length < 2 ^ (prefixWord ++ tailWord_1419295).sum := by decide
  have hdescent : baseEnd_1419295 < baseStart_1419295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419329 : List Nat := [1, 2, 5, 1, 2, 3, 1, 6]
def baseStart_1419329 : Nat := 118140960795 + 1419329 * 2 ^ 59
def prefixEnd_1419329 : Nat := 4983230072969 + 3 ^ 40 * 1419329 * 2
def baseEnd_1419329 : Nat := 107970071683760385549649

theorem tailTrace_1419329 : CollatzResearch.WordTrace tailWord_1419329 prefixEnd_1419329 107970071683760385549649 := by
  unfold tailWord_1419329
  simp only [CollatzResearch.WordTrace]
  refine ⟨51767181475020909939693041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34511454316680606626462027 51767181475020909939693041)
  ·
    refine ⟨38825386106265682454769781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51767181475020909939693041 38825386106265682454769781)
    ·
      refine ⟨3639879947462407730134667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38825386106265682454769781 3639879947462407730134667)
      ·
        refine ⟨5459819921193611595202001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639879947462407730134667 5459819921193611595202001)
        ·
          refine ⟨4094864940895208696401501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5459819921193611595202001 4094864940895208696401501)
          ·
            refine ⟨1535574352835703261150563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4094864940895208696401501 1535574352835703261150563)
            ·
              refine ⟨2303361529253554891725845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535574352835703261150563 2303361529253554891725845)
              ·
                refine ⟨107970071683760385549649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2303361529253554891725845 107970071683760385549649)
                ·
                  rfl

theorem cell21_1419329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 6].length) (baseStart_1419329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419329 prefixEnd_1419329 := by exact prefixLift 1419329
  have htrace : WordTrace (prefixWord ++ tailWord_1419329) baseStart_1419329 baseEnd_1419329 := by
    simpa [prefixWord, tailWord_1419329, baseEnd_1419329] using wordTrace_append hprefix tailTrace_1419329
  have hstable : (prefixWord ++ tailWord_1419329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419329).length < 2 ^ (prefixWord ++ tailWord_1419329).sum := by decide
  have hdescent : baseEnd_1419329 < baseStart_1419329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419360 : List Nat := [2, 1, 1, 3, 2, 4, 2, 3, 3]
def baseStart_1419360 : Nat := 118140960795 + 1419360 * 2 ^ 59
def prefixEnd_1419360 : Nat := 4983230072969 + 3 ^ 40 * 1419360 * 2
def baseEnd_1419360 : Nat := 323917289673631991632217

theorem tailTrace_1419360 : CollatzResearch.WordTrace tailWord_1419360 prefixEnd_1419360 323917289673631991632217 := by
  unfold tailWord_1419360
  simp only [CollatzResearch.WordTrace]
  refine ⟨25884156068954301117035767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34512208091939068156047689 25884156068954301117035767)
  ·
    refine ⟨38826234103431451675553651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25884156068954301117035767 38826234103431451675553651)
    ·
      refine ⟨58239351155147177513330477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38826234103431451675553651 58239351155147177513330477)
      ·
        refine ⟨21839756683180191567498929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58239351155147177513330477 21839756683180191567498929)
        ·
          refine ⟨16379817512385143675624197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21839756683180191567498929 16379817512385143675624197)
          ·
            refine ⟨3071215783572214439179537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16379817512385143675624197 3071215783572214439179537)
            ·
              refine ⟨2303411837679160829384653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3071215783572214439179537 2303411837679160829384653)
              ·
                refine ⟨863779439129685311019245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2303411837679160829384653 863779439129685311019245)
                ·
                  refine ⟨323917289673631991632217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863779439129685311019245 323917289673631991632217)
                  ·
                    rfl

theorem cell21_1419360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_1419360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419360 prefixEnd_1419360 := by exact prefixLift 1419360
  have htrace : WordTrace (prefixWord ++ tailWord_1419360) baseStart_1419360 baseEnd_1419360 := by
    simpa [prefixWord, tailWord_1419360, baseEnd_1419360] using wordTrace_append hprefix tailTrace_1419360
  have hstable : (prefixWord ++ tailWord_1419360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419360).length < 2 ^ (prefixWord ++ tailWord_1419360).sum := by decide
  have hdescent : baseEnd_1419360 < baseStart_1419360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419422 : List Nat := [4, 3, 1, 1, 4, 1, 7]
def baseStart_1419422 : Nat := 118140960795 + 1419422 * 2 ^ 59
def prefixEnd_1419422 : Nat := 4983230072969 + 3 ^ 40 * 1419422 * 2
def baseEnd_1419422 : Nat := 35992382102037073510973

theorem tailTrace_1419422 : CollatzResearch.WordTrace tailWord_1419422 prefixEnd_1419422 35992382102037073510973 := by
  unfold tailWord_1419422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6471321682960498352853565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34513715642455991215219013 6471321682960498352853565)
  ·
    refine ⟨2426745631110186882320087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6471321682960498352853565 2426745631110186882320087)
    ·
      refine ⟨3640118446665280323480131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2426745631110186882320087 3640118446665280323480131)
      ·
        refine ⟨5460177669997920485220197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640118446665280323480131 5460177669997920485220197)
        ·
          refine ⟨1023783313124610090978787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5460177669997920485220197 1023783313124610090978787)
          ·
            refine ⟨1535674969686915136468181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023783313124610090978787 1535674969686915136468181)
            ·
              refine ⟨35992382102037073510973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1535674969686915136468181 35992382102037073510973)
              ·
                rfl

theorem cell21_1419422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 7].length) (baseStart_1419422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419422 prefixEnd_1419422 := by exact prefixLift 1419422
  have htrace : WordTrace (prefixWord ++ tailWord_1419422) baseStart_1419422 baseEnd_1419422 := by
    simpa [prefixWord, tailWord_1419422, baseEnd_1419422] using wordTrace_append hprefix tailTrace_1419422
  have hstable : (prefixWord ++ tailWord_1419422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419422).length < 2 ^ (prefixWord ++ tailWord_1419422).sum := by decide
  have hdescent : baseEnd_1419422 < baseStart_1419422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419447 : List Nat := [1, 1, 3, 1, 4, 2, 1, 8]
def baseStart_1419447 : Nat := 118140960795 + 1419447 * 2 ^ 59
def prefixEnd_1419447 : Nat := 4983230072969 + 3 ^ 40 * 1419447 * 2
def baseEnd_1419447 : Nat := 107979048086313057894013

theorem tailTrace_1419447 : CollatzResearch.WordTrace tailWord_1419447 prefixEnd_1419447 107979048086313057894013 := by
  unfold tailWord_1419447
  simp only [CollatzResearch.WordTrace]
  refine ⟨51771485288593416092488595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34514323525728944061659063 51771485288593416092488595)
  ·
    refine ⟨77657227932890124138732893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51771485288593416092488595 77657227932890124138732893)
    ·
      refine ⟨29121460474833796552024835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77657227932890124138732893 29121460474833796552024835)
      ·
        refine ⟨43682190712250694828037253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29121460474833796552024835 43682190712250694828037253)
        ·
          refine ⟨8190410758547005280256985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43682190712250694828037253 8190410758547005280256985)
          ·
            refine ⟨6142808068910253960192739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8190410758547005280256985 6142808068910253960192739)
            ·
              refine ⟨9214212103365380940289109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6142808068910253960192739 9214212103365380940289109)
              ·
                refine ⟨107979048086313057894013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9214212103365380940289109 107979048086313057894013)
                ·
                  rfl

theorem cell21_1419447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 8].length) (baseStart_1419447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419447 prefixEnd_1419447 := by exact prefixLift 1419447
  have htrace : WordTrace (prefixWord ++ tailWord_1419447) baseStart_1419447 baseEnd_1419447 := by
    simpa [prefixWord, tailWord_1419447, baseEnd_1419447] using wordTrace_append hprefix tailTrace_1419447
  have hstable : (prefixWord ++ tailWord_1419447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419447).length < 2 ^ (prefixWord ++ tailWord_1419447).sum := by decide
  have hdescent : baseEnd_1419447 < baseStart_1419447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419450 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_1419450 : Nat := 118140960795 + 1419450 * 2 ^ 59
def prefixEnd_1419450 : Nat := 4983230072969 + 3 ^ 40 * 1419450 * 2
def baseEnd_1419450 : Nat := 323937828899811835132033

theorem tailTrace_1419450 : CollatzResearch.WordTrace tailWord_1419450 prefixEnd_1419450 323937828899811835132033 := by
  unfold tailWord_1419450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12942898676895636901211951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34514396471721698403231869 12942898676895636901211951)
  ·
    refine ⟨19414348015343455351817927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12942898676895636901211951 19414348015343455351817927)
    ·
      refine ⟨29121522023015183027726891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19414348015343455351817927 29121522023015183027726891)
      ·
        refine ⟨43682283034522774541590337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29121522023015183027726891 43682283034522774541590337)
        ·
          refine ⟨32761712275892080906192753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43682283034522774541590337 32761712275892080906192753)
          ·
            refine ⟨24571284206919060679644565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32761712275892080906192753 24571284206919060679644565)
            ·
              refine ⟨1151778947199330969358339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24571284206919060679644565 1151778947199330969358339)
              ·
                refine ⟨1727668420798996454037509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151778947199330969358339 1727668420798996454037509)
                ·
                  refine ⟨323937828899811835132033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727668420798996454037509 323937828899811835132033)
                  ·
                    rfl

theorem cell21_1419450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_1419450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419450 prefixEnd_1419450 := by exact prefixLift 1419450
  have htrace : WordTrace (prefixWord ++ tailWord_1419450) baseStart_1419450 baseEnd_1419450 := by
    simpa [prefixWord, tailWord_1419450, baseEnd_1419450] using wordTrace_append hprefix tailTrace_1419450
  have hstable : (prefixWord ++ tailWord_1419450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419450).length < 2 ^ (prefixWord ++ tailWord_1419450).sum := by decide
  have hdescent : baseEnd_1419450 < baseStart_1419450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419484 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_1419484 : Nat := 118140960795 + 1419484 * 2 ^ 59
def prefixEnd_1419484 : Nat := 4983230072969 + 3 ^ 40 * 1419484 * 2
def baseEnd_1419484 : Nat := 323945588163035331565297

theorem tailTrace_1419484 : CollatzResearch.WordTrace tailWord_1419484 prefixEnd_1419484 323945588163035331565297 := by
  unfold tailWord_1419484
  simp only [CollatzResearch.WordTrace]
  refine ⟨25886417394729685705792753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34515223192972914274390337 25886417394729685705792753)
  ·
    refine ⟨19414813046047264279344565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25886417394729685705792753 19414813046047264279344565)
    ·
      refine ⟨1820138723066931026188553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19414813046047264279344565 1820138723066931026188553)
      ·
        refine ⟨1365104042300198269641415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1820138723066931026188553 1365104042300198269641415)
        ·
          refine ⟨2047656063450297404462123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365104042300198269641415 2047656063450297404462123)
          ·
            refine ⟨3071484095175446106693185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047656063450297404462123 3071484095175446106693185)
            ·
              refine ⟨2303613071381584580019889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3071484095175446106693185 2303613071381584580019889)
              ·
                refine ⟨1727709803536188435014917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2303613071381584580019889 1727709803536188435014917)
                ·
                  refine ⟨323945588163035331565297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727709803536188435014917 323945588163035331565297)
                  ·
                    rfl

theorem cell21_1419484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_1419484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419484 prefixEnd_1419484 := by exact prefixLift 1419484
  have htrace : WordTrace (prefixWord ++ tailWord_1419484) baseStart_1419484 baseEnd_1419484 := by
    simpa [prefixWord, tailWord_1419484, baseEnd_1419484] using wordTrace_append hprefix tailTrace_1419484
  have hstable : (prefixWord ++ tailWord_1419484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419484).length < 2 ^ (prefixWord ++ tailWord_1419484).sum := by decide
  have hdescent : baseEnd_1419484 < baseStart_1419484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419605 : List Nat := [1, 3, 2, 2, 4, 1, 3, 2, 3]
def baseStart_1419605 : Nat := 118140960795 + 1419605 * 2 ^ 59
def prefixEnd_1419605 : Nat := 4983230072969 + 3 ^ 40 * 1419605 * 2
def baseEnd_1419605 : Nat := 323973202011566010048383

theorem tailTrace_1419605 : CollatzResearch.WordTrace tailWord_1419605 prefixEnd_1419605 323973202011566010048383 := by
  unfold tailWord_1419605
  simp only [CollatzResearch.WordTrace]
  refine ⟨51777248022021009076740269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34518165348014006051160179 51777248022021009076740269)
  ·
    refine ⟨19416468008257878403777601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51777248022021009076740269 19416468008257878403777601)
    ·
      refine ⟨14562351006193408802833201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19416468008257878403777601 14562351006193408802833201)
      ·
        refine ⟨10921763254645056602124901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14562351006193408802833201 10921763254645056602124901)
        ·
          refine ⟨2047830610245948112898419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10921763254645056602124901 2047830610245948112898419)
          ·
            refine ⟨3071745915368922169347629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047830610245948112898419 3071745915368922169347629)
            ·
              refine ⟨1151904718263345813505361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3071745915368922169347629 1151904718263345813505361)
              ·
                refine ⟨863928538697509360129021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151904718263345813505361 863928538697509360129021)
                ·
                  refine ⟨323973202011566010048383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863928538697509360129021 323973202011566010048383)
                  ·
                    rfl

theorem cell21_1419605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_1419605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419605 prefixEnd_1419605 := by exact prefixLift 1419605
  have htrace : WordTrace (prefixWord ++ tailWord_1419605) baseStart_1419605 baseEnd_1419605 := by
    simpa [prefixWord, tailWord_1419605, baseEnd_1419605] using wordTrace_append hprefix tailTrace_1419605
  have hstable : (prefixWord ++ tailWord_1419605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419605).length < 2 ^ (prefixWord ++ tailWord_1419605).sum := by decide
  have hdescent : baseEnd_1419605 < baseStart_1419605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419616 : List Nat := [2, 1, 1, 3, 5, 1, 2, 6]
def baseStart_1419616 : Nat := 118140960795 + 1419616 * 2 ^ 59
def prefixEnd_1419616 : Nat := 4983230072969 + 3 ^ 40 * 1419616 * 2
def baseEnd_1419616 : Nat := 107991904120477478455009

theorem tailTrace_1419616 : CollatzResearch.WordTrace tailWord_1419616 prefixEnd_1419616 107991904120477478455009 := by
  unfold tailWord_1419616
  simp only [CollatzResearch.WordTrace]
  refine ⟨25888824612490578977695351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34518432816654105303593801 25888824612490578977695351)
  ·
    refine ⟨38833236918735868466543027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25888824612490578977695351 38833236918735868466543027)
    ·
      refine ⟨58249855378103802699814541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38833236918735868466543027 58249855378103802699814541)
      ·
        refine ⟨21843695766788926012430453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58249855378103802699814541 21843695766788926012430453)
        ·
          refine ⟨2047846478136461813665355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21843695766788926012430453 2047846478136461813665355)
          ·
            refine ⟨3071769717204692720498033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047846478136461813665355 3071769717204692720498033)
            ·
              refine ⟨2303827287903519540373525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3071769717204692720498033 2303827287903519540373525)
              ·
                refine ⟨107991904120477478455009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2303827287903519540373525 107991904120477478455009)
                ·
                  rfl

theorem cell21_1419616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_1419616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419616 prefixEnd_1419616 := by exact prefixLift 1419616
  have htrace : WordTrace (prefixWord ++ tailWord_1419616) baseStart_1419616 baseEnd_1419616 := by
    simpa [prefixWord, tailWord_1419616, baseEnd_1419616] using wordTrace_append hprefix tailTrace_1419616
  have hstable : (prefixWord ++ tailWord_1419616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419616).length < 2 ^ (prefixWord ++ tailWord_1419616).sum := by decide
  have hdescent : baseEnd_1419616 < baseStart_1419616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419644 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_1419644 : Nat := 118140960795 + 1419644 * 2 ^ 59
def prefixEnd_1419644 : Nat := 4983230072969 + 3 ^ 40 * 1419644 * 2
def baseEnd_1419644 : Nat := 323982102342910608898303

theorem tailTrace_1419644 : CollatzResearch.WordTrace tailWord_1419644 prefixEnd_1419644 323982102342910608898303 := by
  unfold tailWord_1419644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25889335234439859368704993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34519113645919812491606657 25889335234439859368704993)
  ·
    refine ⟨19417001425829894526528745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25889335234439859368704993 19417001425829894526528745)
    ·
      refine ⟨14562751069372420894896559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19417001425829894526528745 14562751069372420894896559)
      ·
        refine ⟨21844126604058631342344839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14562751069372420894896559 21844126604058631342344839)
        ·
          refine ⟨32766189906087947013517259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21844126604058631342344839 32766189906087947013517259)
          ·
            refine ⟨49149284859131920520275889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32766189906087947013517259 49149284859131920520275889)
            ·
              refine ⟨36861963644348940390206917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49149284859131920520275889 36861963644348940390206917)
              ·
                refine ⟨6911618183315426323163797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36861963644348940390206917 6911618183315426323163797)
                ·
                  refine ⟨323982102342910608898303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6911618183315426323163797 323982102342910608898303)
                  ·
                    rfl

theorem cell21_1419644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_1419644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419644 prefixEnd_1419644 := by exact prefixLift 1419644
  have htrace : WordTrace (prefixWord ++ tailWord_1419644) baseStart_1419644 baseEnd_1419644 := by
    simpa [prefixWord, tailWord_1419644, baseEnd_1419644] using wordTrace_append hprefix tailTrace_1419644
  have hstable : (prefixWord ++ tailWord_1419644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419644).length < 2 ^ (prefixWord ++ tailWord_1419644).sum := by decide
  have hdescent : baseEnd_1419644 < baseStart_1419644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419751 : List Nat := [1, 1, 5, 2, 1, 1, 3, 7]
def baseStart_1419751 : Nat := 118140960795 + 1419751 * 2 ^ 59
def prefixEnd_1419751 : Nat := 4983230072969 + 3 ^ 40 * 1419751 * 2
def baseEnd_1419751 : Nat := 108002173733567400204917

theorem tailTrace_1419751 : CollatzResearch.WordTrace tailWord_1419751 prefixEnd_1419751 108002173733567400204917 := by
  unfold tailWord_1419751
  simp only [CollatzResearch.WordTrace]
  refine ⟨51782573079492076011555107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34521715386328050674370071 51782573079492076011555107)
  ·
    refine ⟨77673859619238114017332661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51782573079492076011555107 77673859619238114017332661)
    ·
      refine ⟨7281924339303573189124937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77673859619238114017332661 7281924339303573189124937)
      ·
        refine ⟨5461443254477679891843703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7281924339303573189124937 5461443254477679891843703)
        ·
          refine ⟨8192164881716519837765555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5461443254477679891843703 8192164881716519837765555)
          ·
            refine ⟨12288247322574779756648333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8192164881716519837765555 12288247322574779756648333)
            ·
              refine ⟨4608092745965542408743125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12288247322574779756648333 4608092745965542408743125)
              ·
                refine ⟨108002173733567400204917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4608092745965542408743125 108002173733567400204917)
                ·
                  rfl

theorem cell21_1419751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 7].length) (baseStart_1419751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419751 prefixEnd_1419751 := by exact prefixLift 1419751
  have htrace : WordTrace (prefixWord ++ tailWord_1419751) baseStart_1419751 baseEnd_1419751 := by
    simpa [prefixWord, tailWord_1419751, baseEnd_1419751] using wordTrace_append hprefix tailTrace_1419751
  have hstable : (prefixWord ++ tailWord_1419751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419751).length < 2 ^ (prefixWord ++ tailWord_1419751).sum := by decide
  have hdescent : baseEnd_1419751 < baseStart_1419751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419757 : List Nat := [1, 5, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1419757 : Nat := 118140960795 + 1419757 * 2 ^ 59
def prefixEnd_1419757 : Nat := 4983230072969 + 3 ^ 40 * 1419757 * 2
def baseEnd_1419757 : Nat := 324007890482447523514739

theorem tailTrace_1419757 : CollatzResearch.WordTrace tailWord_1419757 prefixEnd_1419757 324007890482447523514739 := by
  unfold tailWord_1419757
  simp only [CollatzResearch.WordTrace]
  refine ⟨51782791917470339036273525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34521861278313559357515683 51782791917470339036273525)
  ·
    refine ⟨4854636742262844284650643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51782791917470339036273525 4854636742262844284650643)
    ·
      refine ⟨7281955113394266426975965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4854636742262844284650643 7281955113394266426975965)
      ·
        refine ⟨2730733167522849910115987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7281955113394266426975965 2730733167522849910115987)
        ·
          refine ⟨4096099751284274865173981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730733167522849910115987 4096099751284274865173981)
          ·
            refine ⟨1536037406731603074440243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4096099751284274865173981 1536037406731603074440243)
            ·
              refine ⟨2304056110097404611660365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536037406731603074440243 2304056110097404611660365)
              ·
                refine ⟨864021041286526729372637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2304056110097404611660365 864021041286526729372637)
                ·
                  refine ⟨324007890482447523514739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864021041286526729372637 324007890482447523514739)
                  ·
                    rfl

theorem cell21_1419757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1419757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419757 prefixEnd_1419757 := by exact prefixLift 1419757
  have htrace : WordTrace (prefixWord ++ tailWord_1419757) baseStart_1419757 baseEnd_1419757 := by
    simpa [prefixWord, tailWord_1419757, baseEnd_1419757] using wordTrace_append hprefix tailTrace_1419757
  have hstable : (prefixWord ++ tailWord_1419757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419757).length < 2 ^ (prefixWord ++ tailWord_1419757).sum := by decide
  have hdescent : baseEnd_1419757 < baseStart_1419757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419830 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1419830 : Nat := 118140960795 + 1419830 * 2 ^ 59
def prefixEnd_1419830 : Nat := 4983230072969 + 3 ^ 40 * 1419830 * 2
def baseEnd_1419830 : Nat := 324024550077015618797923

theorem tailTrace_1419830 : CollatzResearch.WordTrace tailWord_1419830 prefixEnd_1419830 324024550077015618797923 := by
  unfold tailWord_1419830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236590902887867031480059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34523636297470581669120629 3236590902887867031480059)
  ·
    refine ⟨4854886354331800547220089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3236590902887867031480059 4854886354331800547220089)
    ·
      refine ⟨3641164765748850410415067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4854886354331800547220089 3641164765748850410415067)
      ·
        refine ⟨5461747148623275615622601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3641164765748850410415067 5461747148623275615622601)
        ·
          refine ⟨4096310361467456711716951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5461747148623275615622601 4096310361467456711716951)
          ·
            refine ⟨6144465542201185067575427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096310361467456711716951 6144465542201185067575427)
            ·
              refine ⟨9216698313301777601363141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6144465542201185067575427 9216698313301777601363141)
              ·
                refine ⟨1728130933744083300255589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9216698313301777601363141 1728130933744083300255589)
                ·
                  refine ⟨324024550077015618797923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1728130933744083300255589 324024550077015618797923)
                  ·
                    rfl

theorem cell21_1419830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1419830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419830 prefixEnd_1419830 := by exact prefixLift 1419830
  have htrace : WordTrace (prefixWord ++ tailWord_1419830) baseStart_1419830 baseEnd_1419830 := by
    simpa [prefixWord, tailWord_1419830, baseEnd_1419830] using wordTrace_append hprefix tailTrace_1419830
  have hstable : (prefixWord ++ tailWord_1419830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419830).length < 2 ^ (prefixWord ++ tailWord_1419830).sum := by decide
  have hdescent : baseEnd_1419830 < baseStart_1419830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419858 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1419858 : Nat := 118140960795 + 1419858 * 2 ^ 59
def prefixEnd_1419858 : Nat := 4983230072969 + 3 ^ 40 * 1419858 * 2
def baseEnd_1419858 : Nat := 324030940058493792331199

theorem tailTrace_1419858 : CollatzResearch.WordTrace tailWord_1419858 prefixEnd_1419858 324030940058493792331199 := by
  unfold tailWord_1419858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12946618922526108321425057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34524317126736288857133485 12946618922526108321425057)
  ·
    refine ⟨9709964191894581241068793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12946618922526108321425057 9709964191894581241068793)
    ·
      refine ⟨7282473143920935930801595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9709964191894581241068793 7282473143920935930801595)
      ·
        refine ⟨10923709715881403896202393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7282473143920935930801595 10923709715881403896202393)
        ·
          refine ⟨8192782286911052922151795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10923709715881403896202393 8192782286911052922151795)
          ·
            refine ⟨12289173430366579383227693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8192782286911052922151795 12289173430366579383227693)
            ·
              refine ⟨4608440036387467268710385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12289173430366579383227693 4608440036387467268710385)
              ·
                refine ⟨3456330027290600451532789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4608440036387467268710385 3456330027290600451532789)
                ·
                  refine ⟨324030940058493792331199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3456330027290600451532789 324030940058493792331199)
                  ·
                    rfl

theorem cell21_1419858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1419858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419858 prefixEnd_1419858 := by exact prefixLift 1419858
  have htrace : WordTrace (prefixWord ++ tailWord_1419858) baseStart_1419858 baseEnd_1419858 := by
    simpa [prefixWord, tailWord_1419858, baseEnd_1419858] using wordTrace_append hprefix tailTrace_1419858
  have hstable : (prefixWord ++ tailWord_1419858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419858).length < 2 ^ (prefixWord ++ tailWord_1419858).sum := by decide
  have hdescent : baseEnd_1419858 < baseStart_1419858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419875 : List Nat := [1, 1, 1, 5, 1, 2, 4, 3, 3]
def baseStart_1419875 : Nat := 118140960795 + 1419875 * 2 ^ 59
def prefixEnd_1419875 : Nat := 4983230072969 + 3 ^ 40 * 1419875 * 2
def baseEnd_1419875 : Nat := 324034819690105540547831

theorem tailTrace_1419875 : CollatzResearch.WordTrace tailWord_1419875 prefixEnd_1419875 324034819690105540547831 := by
  unfold tailWord_1419875
  simp only [CollatzResearch.WordTrace]
  refine ⟨51787095731042845189069079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34524730487361896792712719 51787095731042845189069079)
  ·
    refine ⟨77680643596564267783603619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51787095731042845189069079 77680643596564267783603619)
    ·
      refine ⟨116520965394846401675405429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77680643596564267783603619 116520965394846401675405429)
      ·
        refine ⟨10923840505766850157069259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116520965394846401675405429 10923840505766850157069259)
        ·
          refine ⟨16385760758650275235603889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10923840505766850157069259 16385760758650275235603889)
          ·
            refine ⟨12289320568987706426702917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16385760758650275235603889 12289320568987706426702917)
            ·
              refine ⟨2304247606685194955006797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12289320568987706426702917 2304247606685194955006797)
              ·
                refine ⟨864092852506948108127549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2304247606685194955006797 864092852506948108127549)
                ·
                  refine ⟨324034819690105540547831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864092852506948108127549 324034819690105540547831)
                  ·
                    rfl

theorem cell21_1419875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 3].length) (baseStart_1419875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419875 prefixEnd_1419875 := by exact prefixLift 1419875
  have htrace : WordTrace (prefixWord ++ tailWord_1419875) baseStart_1419875 baseEnd_1419875 := by
    simpa [prefixWord, tailWord_1419875, baseEnd_1419875] using wordTrace_append hprefix tailTrace_1419875
  have hstable : (prefixWord ++ tailWord_1419875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419875).length < 2 ^ (prefixWord ++ tailWord_1419875).sum := by decide
  have hdescent : baseEnd_1419875 < baseStart_1419875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419965 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 4]
def baseStart_1419965 : Nat := 118140960795 + 1419965 * 2 ^ 59
def prefixEnd_1419965 : Nat := 4983230072969 + 3 ^ 40 * 1419965 * 2
def baseEnd_1419965 : Nat := 324055358916285384047647

theorem tailTrace_1419965 : CollatzResearch.WordTrace tailWord_1419965 prefixEnd_1419965 324055358916285384047647 := by
  unfold tailWord_1419965
  simp only [CollatzResearch.WordTrace]
  refine ⟨51790378300716790559845349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34526918867144527039896899 51790378300716790559845349)
  ·
    refine ⟨9710695931384398229971003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51790378300716790559845349 9710695931384398229971003)
    ·
      refine ⟨14566043897076597344956505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9710695931384398229971003 14566043897076597344956505)
      ·
        refine ⟨10924532922807448008717379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14566043897076597344956505 10924532922807448008717379)
        ·
          refine ⟨16386799384211172013076069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10924532922807448008717379 16386799384211172013076069)
          ·
            refine ⟨3072524884539594752451763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16386799384211172013076069 3072524884539594752451763)
            ·
              refine ⟨4608787326809392128677645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072524884539594752451763 4608787326809392128677645)
              ·
                refine ⟨1728295247553522048254117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4608787326809392128677645 1728295247553522048254117)
                ·
                  refine ⟨324055358916285384047647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1728295247553522048254117 324055358916285384047647)
                  ·
                    rfl

theorem cell21_1419965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_1419965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1419965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1419965 prefixEnd_1419965 := by exact prefixLift 1419965
  have htrace : WordTrace (prefixWord ++ tailWord_1419965) baseStart_1419965 baseEnd_1419965 := by
    simpa [prefixWord, tailWord_1419965, baseEnd_1419965] using wordTrace_append hprefix tailTrace_1419965
  have hstable : (prefixWord ++ tailWord_1419965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419965).length < 2 ^ (prefixWord ++ tailWord_1419965).sum := by decide
  have hdescent : baseEnd_1419965 < baseStart_1419965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420024 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_1420024 : Nat := 118140960795 + 1420024 * 2 ^ 59
def prefixEnd_1420024 : Nat := 4983230072969 + 3 ^ 40 * 1420024 * 2
def baseEnd_1420024 : Nat := 324068823520114392564193

theorem tailTrace_1420024 : CollatzResearch.WordTrace tailWord_1420024 prefixEnd_1420024 324068823520114392564193 := by
  unfold tailWord_1420024
  simp only [CollatzResearch.WordTrace]
  refine ⟨25896265103751521818121563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34528353471668695757495417 25896265103751521818121563)
  ·
    refine ⟨38844397655627282727182345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25896265103751521818121563 38844397655627282727182345)
    ·
      refine ⟨29133298241720462045386759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38844397655627282727182345 29133298241720462045386759)
      ·
        refine ⟨43699947362580693068080139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29133298241720462045386759 43699947362580693068080139)
        ·
          refine ⟨65549921043871039602120209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43699947362580693068080139 65549921043871039602120209)
          ·
            refine ⟨49162440782903279701590157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65549921043871039602120209 49162440782903279701590157)
            ·
              refine ⟨18435915293588729888096309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49162440782903279701590157 18435915293588729888096309)
              ·
                refine ⟨1728367058773943427009029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18435915293588729888096309 1728367058773943427009029)
                ·
                  refine ⟨324068823520114392564193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1728367058773943427009029 324068823520114392564193)
                  ·
                    rfl

theorem cell21_1420024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_1420024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420024 prefixEnd_1420024 := by exact prefixLift 1420024
  have htrace : WordTrace (prefixWord ++ tailWord_1420024) baseStart_1420024 baseEnd_1420024 := by
    simpa [prefixWord, tailWord_1420024, baseEnd_1420024] using wordTrace_append hprefix tailTrace_1420024
  have hstable : (prefixWord ++ tailWord_1420024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420024).length < 2 ^ (prefixWord ++ tailWord_1420024).sum := by decide
  have hdescent : baseEnd_1420024 < baseStart_1420024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420055 : List Nat := [1, 1, 3, 4, 3, 1, 8]
def baseStart_1420055 : Nat := 118140960795 + 1420055 * 2 ^ 59
def prefixEnd_1420055 : Nat := 4983230072969 + 3 ^ 40 * 1420055 * 2
def baseEnd_1420055 : Nat := 36008433126940580838607

theorem tailTrace_1420055 : CollatzResearch.WordTrace tailWord_1420055 prefixEnd_1420055 36008433126940580838607 := by
  unfold tailWord_1420055
  simp only [CollatzResearch.WordTrace]
  refine ⟨51793660870390735930621619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34529107246927157287081079 51793660870390735930621619)
  ·
    refine ⟨77690491305586103895932429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51793660870390735930621619 77690491305586103895932429)
    ·
      refine ⟨29133934239594788960974661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77690491305586103895932429 29133934239594788960974661)
      ·
        refine ⟨5462612669924022930182749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29133934239594788960974661 5462612669924022930182749)
        ·
          refine ⟨2048479751221508598818531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5462612669924022930182749 2048479751221508598818531)
          ·
            refine ⟨3072719626832262898227797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048479751221508598818531 3072719626832262898227797)
            ·
              refine ⟨36008433126940580838607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3072719626832262898227797 36008433126940580838607)
              ·
                rfl

theorem cell21_1420055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 8].length) (baseStart_1420055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420055 prefixEnd_1420055 := by exact prefixLift 1420055
  have htrace : WordTrace (prefixWord ++ tailWord_1420055) baseStart_1420055 baseEnd_1420055 := by
    simpa [prefixWord, tailWord_1420055, baseEnd_1420055] using wordTrace_append hprefix tailTrace_1420055
  have hstable : (prefixWord ++ tailWord_1420055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420055).length < 2 ^ (prefixWord ++ tailWord_1420055).sum := by decide
  have hdescent : baseEnd_1420055 < baseStart_1420055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420131 : List Nat := [1, 1, 1, 5, 3, 2, 2, 6]
def baseStart_1420131 : Nat := 118140960795 + 1420131 * 2 ^ 59
def prefixEnd_1420131 : Nat := 4983230072969 + 3 ^ 40 * 1420131 * 2
def baseEnd_1420131 : Nat := 108031080792635328093547

theorem tailTrace_1420131 : CollatzResearch.WordTrace tailWord_1420131 prefixEnd_1420131 108031080792635328093547 := by
  unfold tailWord_1420131
  simp only [CollatzResearch.WordTrace]
  refine ⟨51796432818115400910388247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34530955212076933940258831 51796432818115400910388247)
  ·
    refine ⟨77694649227173101365582371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51796432818115400910388247 77694649227173101365582371)
    ·
      refine ⟨116541973840759652048373557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77694649227173101365582371 116541973840759652048373557)
      ·
        refine ⟨10925810047571217379535021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116541973840759652048373557 10925810047571217379535021)
        ·
          refine ⟨4097178767839206517325633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10925810047571217379535021 4097178767839206517325633)
          ·
            refine ⟨3072884075879404887994225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4097178767839206517325633 3072884075879404887994225)
            ·
              refine ⟨2304663056909553665995669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3072884075879404887994225 2304663056909553665995669)
              ·
                refine ⟨108031080792635328093547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2304663056909553665995669 108031080792635328093547)
                ·
                  rfl

theorem cell21_1420131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 6].length) (baseStart_1420131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420131 prefixEnd_1420131 := by exact prefixLift 1420131
  have htrace : WordTrace (prefixWord ++ tailWord_1420131) baseStart_1420131 baseEnd_1420131 := by
    simpa [prefixWord, tailWord_1420131, baseEnd_1420131] using wordTrace_append hprefix tailTrace_1420131
  have hstable : (prefixWord ++ tailWord_1420131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420131).length < 2 ^ (prefixWord ++ tailWord_1420131).sum := by decide
  have hdescent : baseEnd_1420131 < baseStart_1420131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420159 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 8]
def baseStart_1420159 : Nat := 118140960795 + 1420159 * 2 ^ 59
def prefixEnd_1420159 : Nat := 4983230072969 + 3 ^ 40 * 1420159 * 2
def baseEnd_1420159 : Nat := 324099632359384157813917

theorem tailTrace_1420159 : CollatzResearch.WordTrace tailWord_1420159 prefixEnd_1420159 324099632359384157813917 := by
  unfold tailWord_1420159
  simp only [CollatzResearch.WordTrace]
  refine ⟨51797454062013961692407531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34531636041342641128271687 51797454062013961692407531)
  ·
    refine ⟨77696181093020942538611297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51797454062013961692407531 77696181093020942538611297)
    ·
      refine ⟨58272135819765706903958473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77696181093020942538611297 58272135819765706903958473)
      ·
        refine ⟨43704101864824280177968855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58272135819765706903958473 43704101864824280177968855)
        ·
          refine ⟨65556152797236420266953283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43704101864824280177968855 65556152797236420266953283)
          ·
            refine ⟨98334229195854630400429925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65556152797236420266953283 98334229195854630400429925)
            ·
              refine ⟨18437667974222743200080611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98334229195854630400429925 18437667974222743200080611)
              ·
                refine ⟨27656501961334114800120917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18437667974222743200080611 27656501961334114800120917)
                ·
                  refine ⟨324099632359384157813917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27656501961334114800120917 324099632359384157813917)
                  ·
                    rfl

theorem cell21_1420159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_1420159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420159 prefixEnd_1420159 := by exact prefixLift 1420159
  have htrace : WordTrace (prefixWord ++ tailWord_1420159) baseStart_1420159 baseEnd_1420159 := by
    simpa [prefixWord, tailWord_1420159, baseEnd_1420159] using wordTrace_append hprefix tailTrace_1420159
  have hstable : (prefixWord ++ tailWord_1420159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420159).length < 2 ^ (prefixWord ++ tailWord_1420159).sum := by decide
  have hdescent : baseEnd_1420159 < baseStart_1420159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420182 : List Nat := [5, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1420182 : Nat := 118140960795 + 1420182 * 2 ^ 59
def prefixEnd_1420182 : Nat := 4983230072969 + 3 ^ 40 * 1420182 * 2
def baseEnd_1420182 : Nat := 108034960424247076310179

theorem tailTrace_1420182 : CollatzResearch.WordTrace tailWord_1420182 prefixEnd_1420182 108034960424247076310179 := by
  unfold tailWord_1420182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237393308808164788780925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34532195293953757746996533 3237393308808164788780925)
  ·
    refine ⟨1214022490803061795792847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3237393308808164788780925 1214022490803061795792847)
    ·
      refine ⟨1821033736204592693689271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1214022490803061795792847 1821033736204592693689271)
      ·
        refine ⟨2731550604306889040533907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821033736204592693689271 2731550604306889040533907)
        ·
          refine ⟨4097325906460333560800861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731550604306889040533907 4097325906460333560800861)
          ·
            refine ⟨1536497214922625085300323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4097325906460333560800861 1536497214922625085300323)
            ·
              refine ⟨2304745822383937627950485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536497214922625085300323 2304745822383937627950485)
              ·
                refine ⟨108034960424247076310179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2304745822383937627950485 108034960424247076310179)
                ·
                  rfl

theorem cell21_1420182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1420182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420182 prefixEnd_1420182 := by exact prefixLift 1420182
  have htrace : WordTrace (prefixWord ++ tailWord_1420182) baseStart_1420182 baseEnd_1420182 := by
    simpa [prefixWord, tailWord_1420182, baseEnd_1420182] using wordTrace_append hprefix tailTrace_1420182
  have hstable : (prefixWord ++ tailWord_1420182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420182).length < 2 ^ (prefixWord ++ tailWord_1420182).sum := by decide
  have hdescent : baseEnd_1420182 < baseStart_1420182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420193 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 4]
def baseStart_1420193 : Nat := 118140960795 + 1420193 * 2 ^ 59
def prefixEnd_1420193 : Nat := 4983230072969 + 3 ^ 40 * 1420193 * 2
def baseEnd_1420193 : Nat := 324107391622607654247181

theorem tailTrace_1420193 : CollatzResearch.WordTrace tailWord_1420193 prefixEnd_1420193 324107391622607654247181 := by
  unfold tailWord_1420193
  simp only [CollatzResearch.WordTrace]
  refine ⟨51798694143890785499145233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34532462762593856999430155 51798694143890785499145233)
  ·
    refine ⟨38849020607918089124358925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51798694143890785499145233 38849020607918089124358925)
    ·
      refine ⟨14568382727969283421634597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38849020607918089124358925 14568382727969283421634597)
      ·
        refine ⟨2731571761494240641556487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14568382727969283421634597 2731571761494240641556487)
        ·
          refine ⟨4097357642241360962334731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731571761494240641556487 4097357642241360962334731)
          ·
            refine ⟨6146036463362041443502097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097357642241360962334731 6146036463362041443502097)
            ·
              refine ⟨4609527347521531082626573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6146036463362041443502097 4609527347521531082626573)
              ·
                refine ⟨1728572755320574155984965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4609527347521531082626573 1728572755320574155984965)
                ·
                  refine ⟨324107391622607654247181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1728572755320574155984965 324107391622607654247181)
                  ·
                    rfl

theorem cell21_1420193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_1420193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420193 prefixEnd_1420193 := by exact prefixLift 1420193
  have htrace : WordTrace (prefixWord ++ tailWord_1420193) baseStart_1420193 baseEnd_1420193 := by
    simpa [prefixWord, tailWord_1420193, baseEnd_1420193] using wordTrace_append hprefix tailTrace_1420193
  have hstable : (prefixWord ++ tailWord_1420193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420193).length < 2 ^ (prefixWord ++ tailWord_1420193).sum := by decide
  have hdescent : baseEnd_1420193 < baseStart_1420193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420230 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1420230 : Nat := 118140960795 + 1420230 * 2 ^ 59
def prefixEnd_1420230 : Nat := 4983230072969 + 3 ^ 40 * 1420230 * 2
def baseEnd_1420230 : Nat := 324115835526703812130439

theorem tailTrace_1420230 : CollatzResearch.WordTrace tailWord_1420230 prefixEnd_1420230 324115835526703812130439 := by
  unfold tailWord_1420230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1618751363898648150570067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34533362429837827212161429 1618751363898648150570067)
  ·
    refine ⟨2428127045847972225855101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1618751363898648150570067 2428127045847972225855101)
    ·
      refine ⟨910547642192989584695663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2428127045847972225855101 910547642192989584695663)
      ·
        refine ⟨1365821463289484377043495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910547642192989584695663 1365821463289484377043495)
        ·
          refine ⟨2048732194934226565565243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365821463289484377043495 2048732194934226565565243)
          ·
            refine ⟨3073098292401339848347865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048732194934226565565243 3073098292401339848347865)
            ·
              refine ⟨2304823719301004886260899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073098292401339848347865 2304823719301004886260899)
              ·
                refine ⟨3457235578951507329391349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304823719301004886260899 3457235578951507329391349)
                ·
                  refine ⟨324115835526703812130439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3457235578951507329391349 324115835526703812130439)
                  ·
                    rfl

theorem cell21_1420230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1420230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420230 prefixEnd_1420230 := by exact prefixLift 1420230
  have htrace : WordTrace (prefixWord ++ tailWord_1420230) baseStart_1420230 baseEnd_1420230 := by
    simpa [prefixWord, tailWord_1420230, baseEnd_1420230] using wordTrace_append hprefix tailTrace_1420230
  have hstable : (prefixWord ++ tailWord_1420230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420230).length < 2 ^ (prefixWord ++ tailWord_1420230).sum := by decide
  have hdescent : baseEnd_1420230 < baseStart_1420230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420238 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_1420238 : Nat := 118140960795 + 1420238 * 2 ^ 59
def prefixEnd_1420238 : Nat := 4983230072969 + 3 ^ 40 * 1420238 * 2
def baseEnd_1420238 : Nat := 324117661235697575997089

theorem tailTrace_1420238 : CollatzResearch.WordTrace tailWord_1420238 prefixEnd_1420238 324117661235697575997089 := by
  unfold tailWord_1420238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475041928590969773066671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34533556952485172123022245 6475041928590969773066671)
  ·
    refine ⟨9712562892886454659600007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6475041928590969773066671 9712562892886454659600007)
    ·
      refine ⟨14568844339329681989400011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9712562892886454659600007 14568844339329681989400011)
      ·
        refine ⟨21853266508994522984100017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14568844339329681989400011 21853266508994522984100017)
        ·
          refine ⟨16389949881745892238075013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21853266508994522984100017 16389949881745892238075013)
          ·
            refine ⟨3073115602827354794639065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16389949881745892238075013 3073115602827354794639065)
            ·
              refine ⟨2304836702120516095979299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073115602827354794639065 2304836702120516095979299)
              ·
                refine ⟨3457255053180774143968949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304836702120516095979299 3457255053180774143968949)
                ·
                  refine ⟨324117661235697575997089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3457255053180774143968949 324117661235697575997089)
                  ·
                    rfl

theorem cell21_1420238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_1420238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420238 prefixEnd_1420238 := by exact prefixLift 1420238
  have htrace : WordTrace (prefixWord ++ tailWord_1420238) baseStart_1420238 baseEnd_1420238 := by
    simpa [prefixWord, tailWord_1420238, baseEnd_1420238] using wordTrace_append hprefix tailTrace_1420238
  have hstable : (prefixWord ++ tailWord_1420238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420238).length < 2 ^ (prefixWord ++ tailWord_1420238).sum := by decide
  have hdescent : baseEnd_1420238 < baseStart_1420238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420345 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 4]
def baseStart_1420345 : Nat := 118140960795 + 1420345 * 2 ^ 59
def prefixEnd_1420345 : Nat := 4983230072969 + 3 ^ 40 * 1420345 * 2
def baseEnd_1420345 : Nat := 324142080093489167713537

theorem tailTrace_1420345 : CollatzResearch.WordTrace tailWord_1420345 prefixEnd_1420345 324142080093489167713537 := by
  unfold tailWord_1420345
  simp only [CollatzResearch.WordTrace]
  refine ⟨51804238039340115458678489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34536158692893410305785659 51804238039340115458678489)
  ·
    refine ⟨38853178529505086594008867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51804238039340115458678489 38853178529505086594008867)
    ·
      refine ⟨58279767794257629891013301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38853178529505086594008867 58279767794257629891013301)
      ·
        refine ⟨5463728230711652802282497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58279767794257629891013301 5463728230711652802282497)
        ·
          refine ⟨4097796173033739601711873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5463728230711652802282497 4097796173033739601711873)
          ·
            refine ⟨3073347129775304701283905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4097796173033739601711873 3073347129775304701283905)
            ·
              refine ⟨2305010347331478525962929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073347129775304701283905 2305010347331478525962929)
              ·
                refine ⟨1728757760498608894472197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2305010347331478525962929 1728757760498608894472197)
                ·
                  refine ⟨324142080093489167713537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1728757760498608894472197 324142080093489167713537)
                  ·
                    rfl

theorem cell21_1420345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_1420345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420345 prefixEnd_1420345 := by exact prefixLift 1420345
  have htrace : WordTrace (prefixWord ++ tailWord_1420345) baseStart_1420345 baseEnd_1420345 := by
    simpa [prefixWord, tailWord_1420345, baseEnd_1420345] using wordTrace_append hprefix tailTrace_1420345
  have hstable : (prefixWord ++ tailWord_1420345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420345).length < 2 ^ (prefixWord ++ tailWord_1420345).sum := by decide
  have hdescent : baseEnd_1420345 < baseStart_1420345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420348 : List Nat := [2, 2, 2, 2, 2, 4, 2, 2, 3]
def baseStart_1420348 : Nat := 118140960795 + 1420348 * 2 ^ 59
def prefixEnd_1420348 : Nat := 4983230072969 + 3 ^ 40 * 1420348 * 2
def baseEnd_1420348 : Nat := 324142764734361829163531

theorem tailTrace_1420348 : CollatzResearch.WordTrace tailWord_1420348 prefixEnd_1420348 324142764734361829163531 := by
  unfold tailWord_1420348
  simp only [CollatzResearch.WordTrace]
  refine ⟨25902173729164623485518849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34536231638886164647358465 25902173729164623485518849)
  ·
    refine ⟨19426630296873467614139137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25902173729164623485518849 19426630296873467614139137)
    ·
      refine ⟨14569972722655100710604353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19426630296873467614139137 14569972722655100710604353)
      ·
        refine ⟨10927479541991325532953265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14569972722655100710604353 10927479541991325532953265)
        ·
          refine ⟨8195609656493494149714949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10927479541991325532953265 8195609656493494149714949)
          ·
            refine ⟨1536676810592530153071553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8195609656493494149714949 1536676810592530153071553)
            ·
              refine ⟨1152507607944397614803665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536676810592530153071553 1152507607944397614803665)
              ·
                refine ⟨864380705958298211102749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152507607944397614803665 864380705958298211102749)
                ·
                  refine ⟨324142764734361829163531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864380705958298211102749 324142764734361829163531)
                  ·
                    rfl

theorem cell21_1420348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_1420348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420348 prefixEnd_1420348 := by exact prefixLift 1420348
  have htrace : WordTrace (prefixWord ++ tailWord_1420348) baseStart_1420348 baseEnd_1420348 := by
    simpa [prefixWord, tailWord_1420348, baseEnd_1420348] using wordTrace_append hprefix tailTrace_1420348
  have hstable : (prefixWord ++ tailWord_1420348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420348).length < 2 ^ (prefixWord ++ tailWord_1420348).sum := by decide
  have hdescent : baseEnd_1420348 < baseStart_1420348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420359 : List Nat := [1, 1, 4, 1, 3, 4, 1, 6]
def baseStart_1420359 : Nat := 118140960795 + 1420359 * 2 ^ 59
def prefixEnd_1420359 : Nat := 4983230072969 + 3 ^ 40 * 1420359 * 2
def baseEnd_1420359 : Nat := 108048425028076084826725

theorem tailTrace_1420359 : CollatzResearch.WordTrace tailWord_1420359 prefixEnd_1420359 108048425028076084826725 := by
  unfold tailWord_1420359
  simp only [CollatzResearch.WordTrace]
  refine ⟨51804748661289395849688131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34536499107526263899792087 51804748661289395849688131)
  ·
    refine ⟨77707122991934093774532197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51804748661289395849688131 77707122991934093774532197)
    ·
      refine ⟨14570085560987642582724787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77707122991934093774532197 14570085560987642582724787)
      ·
        refine ⟨21855128341481463874087181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14570085560987642582724787 21855128341481463874087181)
        ·
          refine ⟨8195673128055548952782693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21855128341481463874087181 8195673128055548952782693)
          ·
            refine ⟨1536688711510415428646755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8195673128055548952782693 1536688711510415428646755)
            ·
              refine ⟨2305033067265623142970133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536688711510415428646755 2305033067265623142970133)
              ·
                refine ⟨108048425028076084826725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2305033067265623142970133 108048425028076084826725)
                ·
                  rfl

theorem cell21_1420359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 6].length) (baseStart_1420359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420359 prefixEnd_1420359 := by exact prefixLift 1420359
  have htrace : WordTrace (prefixWord ++ tailWord_1420359) baseStart_1420359 baseEnd_1420359 := by
    simpa [prefixWord, tailWord_1420359, baseEnd_1420359] using wordTrace_append hprefix tailTrace_1420359
  have hstable : (prefixWord ++ tailWord_1420359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420359).length < 2 ^ (prefixWord ++ tailWord_1420359).sum := by decide
  have hdescent : baseEnd_1420359 < baseStart_1420359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420373 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 5]
def baseStart_1420373 : Nat := 118140960795 + 1420373 * 2 ^ 59
def prefixEnd_1420373 : Nat := 4983230072969 + 3 ^ 40 * 1420373 * 2
def baseEnd_1420373 : Nat := 324148470074967341246813

theorem tailTrace_1420373 : CollatzResearch.WordTrace tailWord_1420373 prefixEnd_1420373 324148470074967341246813 := by
  unfold tailWord_1420373
  simp only [CollatzResearch.WordTrace]
  refine ⟨51805259283238676240697773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34536839522159117493798515 51805259283238676240697773)
  ·
    refine ⟨19426972231214503590261665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51805259283238676240697773 19426972231214503590261665)
    ·
      refine ⟨14570229173410877692696249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19426972231214503590261665 14570229173410877692696249)
      ·
        refine ⟨10927671880058158269522187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14570229173410877692696249 10927671880058158269522187)
        ·
          refine ⟨16391507820087237404283281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10927671880058158269522187 16391507820087237404283281)
          ·
            refine ⟨12293630865065428053212461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16391507820087237404283281 12293630865065428053212461)
            ·
              refine ⟨4610111574399535519954673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12293630865065428053212461 4610111574399535519954673)
              ·
                refine ⟨3457583680799651639966005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610111574399535519954673 3457583680799651639966005)
                ·
                  refine ⟨324148470074967341246813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3457583680799651639966005 324148470074967341246813)
                  ·
                    rfl

theorem cell21_1420373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_1420373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420373 prefixEnd_1420373 := by exact prefixLift 1420373
  have htrace : WordTrace (prefixWord ++ tailWord_1420373) baseStart_1420373 baseEnd_1420373 := by
    simpa [prefixWord, tailWord_1420373, baseEnd_1420373] using wordTrace_append hprefix tailTrace_1420373
  have hstable : (prefixWord ++ tailWord_1420373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420373).length < 2 ^ (prefixWord ++ tailWord_1420373).sum := by decide
  have hdescent : baseEnd_1420373 < baseStart_1420373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420387 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 6]
def baseStart_1420387 : Nat := 118140960795 + 1420387 * 2 ^ 59
def prefixEnd_1420387 : Nat := 4983230072969 + 3 ^ 40 * 1420387 * 2
def baseEnd_1420387 : Nat := 324151665065706428013451

theorem tailTrace_1420387 : CollatzResearch.WordTrace tailWord_1420387 prefixEnd_1420387 324151665065706428013451 := by
  unfold tailWord_1420387
  simp only [CollatzResearch.WordTrace]
  refine ⟨51805769905187956631707415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34537179936791971087804943 51805769905187956631707415)
  ·
    refine ⟨77708654857781934947561123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51805769905187956631707415 77708654857781934947561123)
    ·
      refine ⟨116562982286672902421341685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77708654857781934947561123 116562982286672902421341685)
      ·
        refine ⟨10927779589375584602000783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116562982286672902421341685 10927779589375584602000783)
        ·
          refine ⟨16391669384063376903001175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10927779589375584602000783 16391669384063376903001175)
          ·
            refine ⟨24587504076095065354501763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16391669384063376903001175 24587504076095065354501763)
            ·
              refine ⟨36881256114142598031752645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24587504076095065354501763 36881256114142598031752645)
              ·
                refine ⟨6915235521401737130953621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36881256114142598031752645 6915235521401737130953621)
                ·
                  refine ⟨324151665065706428013451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6915235521401737130953621 324151665065706428013451)
                  ·
                    rfl

theorem cell21_1420387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_1420387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420387 prefixEnd_1420387 := by exact prefixLift 1420387
  have htrace : WordTrace (prefixWord ++ tailWord_1420387) baseStart_1420387 baseEnd_1420387 := by
    simpa [prefixWord, tailWord_1420387, baseEnd_1420387] using wordTrace_append hprefix tailTrace_1420387
  have hstable : (prefixWord ++ tailWord_1420387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420387).length < 2 ^ (prefixWord ++ tailWord_1420387).sum := by decide
  have hdescent : baseEnd_1420387 < baseStart_1420387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420432 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_1420432 : Nat := 118140960795 + 1420432 * 2 ^ 59
def prefixEnd_1420432 : Nat := 4983230072969 + 3 ^ 40 * 1420432 * 2
def baseEnd_1420432 : Nat := 324161934678796349763359

theorem tailTrace_1420432 : CollatzResearch.WordTrace tailWord_1420432 prefixEnd_1420432 324161934678796349763359 := by
  unfold tailWord_1420432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25903705595012464658547775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34538274126683286211397033 25903705595012464658547775)
  ·
    refine ⟨38855558392518696987821663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25903705595012464658547775 38855558392518696987821663)
    ·
      refine ⟨58283337588778045481732495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38855558392518696987821663 58283337588778045481732495)
      ·
        refine ⟨87425006383167068222598743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58283337588778045481732495 87425006383167068222598743)
        ·
          refine ⟨131137509574750602333898115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87425006383167068222598743 131137509574750602333898115)
          ·
            refine ⟨196706264362125903500847173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131137509574750602333898115 196706264362125903500847173)
            ·
              refine ⟨36882424567898606906408845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196706264362125903500847173 36882424567898606906408845)
              ·
                refine ⟨13830909212961977589903317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36882424567898606906408845 13830909212961977589903317)
                ·
                  refine ⟨324161934678796349763359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13830909212961977589903317 324161934678796349763359)
                  ·
                    rfl

theorem cell21_1420432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_1420432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420432 prefixEnd_1420432 := by exact prefixLift 1420432
  have htrace : WordTrace (prefixWord ++ tailWord_1420432) baseStart_1420432 baseEnd_1420432 := by
    simpa [prefixWord, tailWord_1420432, baseEnd_1420432] using wordTrace_append hprefix tailTrace_1420432
  have hstable : (prefixWord ++ tailWord_1420432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420432).length < 2 ^ (prefixWord ++ tailWord_1420432).sum := by decide
  have hdescent : baseEnd_1420432 < baseStart_1420432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420463 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 6]
def baseStart_1420463 : Nat := 118140960795 + 1420463 * 2 ^ 59
def prefixEnd_1420463 : Nat := 4983230072969 + 3 ^ 40 * 1420463 * 2
def baseEnd_1420463 : Nat := 324169009301147184746629

theorem tailTrace_1420463 : CollatzResearch.WordTrace tailWord_1420463 prefixEnd_1420463 324169009301147184746629 := by
  unfold tailWord_1420463
  simp only [CollatzResearch.WordTrace]
  refine ⟨51808541852912621611474043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34539027901941747740982695 51808541852912621611474043)
  ·
    refine ⟨77712812779368932417211065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51808541852912621611474043 77712812779368932417211065)
    ·
      refine ⟨58284609584526699312908299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77712812779368932417211065 58284609584526699312908299)
      ·
        refine ⟨87426914376790048969362449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58284609584526699312908299 87426914376790048969362449)
        ·
          refine ⟨65570185782592536727021837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87426914376790048969362449 65570185782592536727021837)
          ·
            refine ⟨24588819668472201272633189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65570185782592536727021837 24588819668472201272633189)
            ·
              refine ⟨4610403687838537738618723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24588819668472201272633189 4610403687838537738618723)
              ·
                refine ⟨6915605531757806607928085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4610403687838537738618723 6915605531757806607928085)
                ·
                  refine ⟨324169009301147184746629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6915605531757806607928085 324169009301147184746629)
                  ·
                    rfl

theorem cell21_1420463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_1420463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420463 prefixEnd_1420463 := by exact prefixLift 1420463
  have htrace : WordTrace (prefixWord ++ tailWord_1420463) baseStart_1420463 baseEnd_1420463 := by
    simpa [prefixWord, tailWord_1420463, baseEnd_1420463] using wordTrace_append hprefix tailTrace_1420463
  have hstable : (prefixWord ++ tailWord_1420463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420463).length < 2 ^ (prefixWord ++ tailWord_1420463).sum := by decide
  have hdescent : baseEnd_1420463 < baseStart_1420463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420466 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_1420466 : Nat := 118140960795 + 1420466 * 2 ^ 59
def prefixEnd_1420466 : Nat := 4983230072969 + 3 ^ 40 * 1420466 * 2
def baseEnd_1420466 : Nat := 324169693942019846196623

theorem tailTrace_1420466 : CollatzResearch.WordTrace tailWord_1420466 prefixEnd_1420466 324169693942019846196623 := by
  unfold tailWord_1420466
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952162817975438280958313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34539100847934502082555501 12952162817975438280958313)
  ·
    refine ⟨9714122113481578710718735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12952162817975438280958313 9714122113481578710718735)
    ·
      refine ⟨14571183170222368066078103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9714122113481578710718735 14571183170222368066078103)
      ·
        refine ⟨21856774755333552099117155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14571183170222368066078103 21856774755333552099117155)
        ·
          refine ⟨32785162133000328148675733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21856774755333552099117155 32785162133000328148675733)
          ·
            refine ⟨1536804474984390381969175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32785162133000328148675733 1536804474984390381969175)
            ·
              refine ⟨2305206712476585572953763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536804474984390381969175 2305206712476585572953763)
              ·
                refine ⟨3457810068714878359430645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305206712476585572953763 3457810068714878359430645)
                ·
                  refine ⟨324169693942019846196623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3457810068714878359430645 324169693942019846196623)
                  ·
                    rfl

theorem cell21_1420466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_1420466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420466 prefixEnd_1420466 := by exact prefixLift 1420466
  have htrace : WordTrace (prefixWord ++ tailWord_1420466) baseStart_1420466 baseEnd_1420466 := by
    simpa [prefixWord, tailWord_1420466, baseEnd_1420466] using wordTrace_append hprefix tailTrace_1420466
  have hstable : (prefixWord ++ tailWord_1420466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420466).length < 2 ^ (prefixWord ++ tailWord_1420466).sum := by decide
  have hdescent : baseEnd_1420466 < baseStart_1420466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420517 : List Nat := [1, 3, 1, 4, 4, 1, 2, 2, 3]
def baseStart_1420517 : Nat := 118140960795 + 1420517 * 2 ^ 59
def prefixEnd_1420517 : Nat := 4983230072969 + 3 ^ 40 * 1420517 * 2
def baseEnd_1420517 : Nat := 324181332836855090846519

theorem tailTrace_1420517 : CollatzResearch.WordTrace tailWord_1420517 prefixEnd_1420517 324181332836855090846519 := by
  unfold tailWord_1420517
  simp only [CollatzResearch.WordTrace]
  refine ⟨51810511394716988833939805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34540340929811325889293203 51810511394716988833939805)
  ·
    refine ⟨19428941773018870812727427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51810511394716988833939805 19428941773018870812727427)
    ·
      refine ⟨29143412659528306219091141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19428941773018870812727427 29143412659528306219091141)
      ·
        refine ⟨5464389873661557416079589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29143412659528306219091141 5464389873661557416079589)
        ·
          refine ⟨1024573101311542015514923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5464389873661557416079589 1024573101311542015514923)
          ·
            refine ⟨1536859651967313023272385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024573101311542015514923 1536859651967313023272385)
            ·
              refine ⟨1152644738975484767454289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536859651967313023272385 1152644738975484767454289)
              ·
                refine ⟨864483554231613575590717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152644738975484767454289 864483554231613575590717)
                ·
                  refine ⟨324181332836855090846519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864483554231613575590717 324181332836855090846519)
                  ·
                    rfl

theorem cell21_1420517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_1420517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420517 prefixEnd_1420517 := by exact prefixLift 1420517
  have htrace : WordTrace (prefixWord ++ tailWord_1420517) baseStart_1420517 baseEnd_1420517 := by
    simpa [prefixWord, tailWord_1420517, baseEnd_1420517] using wordTrace_append hprefix tailTrace_1420517
  have hstable : (prefixWord ++ tailWord_1420517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420517).length < 2 ^ (prefixWord ++ tailWord_1420517).sum := by decide
  have hdescent : baseEnd_1420517 < baseStart_1420517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420542 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1420542 : Nat := 118140960795 + 1420542 * 2 ^ 59
def prefixEnd_1420542 : Nat := 4983230072969 + 3 ^ 40 * 1420542 * 2
def baseEnd_1420542 : Nat := 324187038177460602929801

theorem tailTrace_1420542 : CollatzResearch.WordTrace tailWord_1420542 prefixEnd_1420542 324187038177460602929801 := by
  unfold tailWord_1420542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6476427902453302262949985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34540948813084278735733253 6476427902453302262949985)
  ·
    refine ⟨4857320926839976697212489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6476427902453302262949985 4857320926839976697212489)
    ·
      refine ⟨3642990695129982522909367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4857320926839976697212489 3642990695129982522909367)
      ·
        refine ⟨5464486042694973784364051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3642990695129982522909367 5464486042694973784364051)
        ·
          refine ⟨8196729064042460676546077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464486042694973784364051 8196729064042460676546077)
          ·
            refine ⟨3073773399015922753704779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8196729064042460676546077 3073773399015922753704779)
            ·
              refine ⟨4610660098523884130557169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073773399015922753704779 4610660098523884130557169)
              ·
                refine ⟨3457995073892913097917877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610660098523884130557169 3457995073892913097917877)
                ·
                  refine ⟨324187038177460602929801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3457995073892913097917877 324187038177460602929801)
                  ·
                    rfl

theorem cell21_1420542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1420542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420542 prefixEnd_1420542 := by exact prefixLift 1420542
  have htrace : WordTrace (prefixWord ++ tailWord_1420542) baseStart_1420542 baseEnd_1420542 := by
    simpa [prefixWord, tailWord_1420542, baseEnd_1420542] using wordTrace_append hprefix tailTrace_1420542
  have hstable : (prefixWord ++ tailWord_1420542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420542).length < 2 ^ (prefixWord ++ tailWord_1420542).sum := by decide
  have hdescent : baseEnd_1420542 < baseStart_1420542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420570 : List Nat := [3, 1, 1, 3, 3, 2, 8]
def baseStart_1420570 : Nat := 118140960795 + 1420570 * 2 ^ 59
def prefixEnd_1420570 : Nat := 4983230072969 + 3 ^ 40 * 1420570 * 2
def baseEnd_1420570 : Nat := 36021492017659864051453

theorem tailTrace_1420570 : CollatzResearch.WordTrace tailWord_1420570 prefixEnd_1420570 36021492017659864051453 := by
  unfold tailWord_1420570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12953111115881244721404791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34541629642349985923746109 12953111115881244721404791)
  ·
    refine ⟨19429666673821867082107187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12953111115881244721404791 19429666673821867082107187)
    ·
      refine ⟨29144500010732800623160781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19429666673821867082107187 29144500010732800623160781)
      ·
        refine ⟨10929187504024800233685293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29144500010732800623160781 10929187504024800233685293)
        ·
          refine ⟨4098445314009300087631985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10929187504024800233685293 4098445314009300087631985)
          ·
            refine ⟨3073833985506975065723989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4098445314009300087631985 3073833985506975065723989)
            ·
              refine ⟨36021492017659864051453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3073833985506975065723989 36021492017659864051453)
              ·
                rfl

theorem cell21_1420570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 8].length) (baseStart_1420570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420570 prefixEnd_1420570 := by exact prefixLift 1420570
  have htrace : WordTrace (prefixWord ++ tailWord_1420570) baseStart_1420570 baseEnd_1420570 := by
    simpa [prefixWord, tailWord_1420570, baseEnd_1420570] using wordTrace_append hprefix tailTrace_1420570
  have hstable : (prefixWord ++ tailWord_1420570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420570).length < 2 ^ (prefixWord ++ tailWord_1420570).sum := by decide
  have hdescent : baseEnd_1420570 < baseStart_1420570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420573 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 4]
def baseStart_1420573 : Nat := 118140960795 + 1420573 * 2 ^ 59
def prefixEnd_1420573 : Nat := 4983230072969 + 3 ^ 40 * 1420573 * 2
def baseEnd_1420573 : Nat := 324194112799811437913071

theorem tailTrace_1420573 : CollatzResearch.WordTrace tailWord_1420573 prefixEnd_1420573 324194112799811437913071 := by
  unfold tailWord_1420573
  simp only [CollatzResearch.WordTrace]
  refine ⟨51812553882514110397978373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34541702588342740265318915 51812553882514110397978373)
  ·
    refine ⟨9714853852971395699620945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51812553882514110397978373 9714853852971395699620945)
    ·
      refine ⟨7286140389728546774715709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9714853852971395699620945 7286140389728546774715709)
      ·
        refine ⟨2732302646148205040518391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7286140389728546774715709 2732302646148205040518391)
        ·
          refine ⟨4098453969222307560777587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2732302646148205040518391 4098453969222307560777587)
          ·
            refine ⟨6147680953833461341166381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4098453969222307560777587 6147680953833461341166381)
            ·
              refine ⟨2305380357687548002937393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6147680953833461341166381 2305380357687548002937393)
              ·
                refine ⟨1729035268265661002203045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2305380357687548002937393 1729035268265661002203045)
                ·
                  refine ⟨324194112799811437913071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729035268265661002203045 324194112799811437913071)
                  ·
                    rfl

theorem cell21_1420573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_1420573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420573 prefixEnd_1420573 := by exact prefixLift 1420573
  have htrace : WordTrace (prefixWord ++ tailWord_1420573) baseStart_1420573 baseEnd_1420573 := by
    simpa [prefixWord, tailWord_1420573, baseEnd_1420573] using wordTrace_append hprefix tailTrace_1420573
  have hstable : (prefixWord ++ tailWord_1420573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420573).length < 2 ^ (prefixWord ++ tailWord_1420573).sum := by decide
  have hdescent : baseEnd_1420573 < baseStart_1420573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420615 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 6]
def baseStart_1420615 : Nat := 118140960795 + 1420615 * 2 ^ 59
def prefixEnd_1420615 : Nat := 4983230072969 + 3 ^ 40 * 1420615 * 2
def baseEnd_1420615 : Nat := 324203697772028698212985

theorem tailTrace_1420615 : CollatzResearch.WordTrace tailWord_1420615 prefixEnd_1420615 324203697772028698212985 := by
  unfold tailWord_1420615
  simp only [CollatzResearch.WordTrace]
  refine ⟨51814085748361951571007299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34542723832241301047338199 51814085748361951571007299)
  ·
    refine ⟨77721128622542927356510949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51814085748361951571007299 77721128622542927356510949)
    ·
      refine ⟨14572711616726798879345803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77721128622542927356510949 14572711616726798879345803)
      ·
        refine ⟨21859067425090198319018705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14572711616726798879345803 21859067425090198319018705)
        ·
          refine ⟨16394300568817648739264029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21859067425090198319018705 16394300568817648739264029)
          ·
            refine ⟨6147862713306618277224011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16394300568817648739264029 6147862713306618277224011)
            ·
              refine ⟨9221794069959927415836017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147862713306618277224011 9221794069959927415836017)
              ·
                refine ⟨6916345552469945561877013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9221794069959927415836017 6916345552469945561877013)
                ·
                  refine ⟨324203697772028698212985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6916345552469945561877013 324203697772028698212985)
                  ·
                    rfl

theorem cell21_1420615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_1420615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420615 prefixEnd_1420615 := by exact prefixLift 1420615
  have htrace : WordTrace (prefixWord ++ tailWord_1420615) baseStart_1420615 baseEnd_1420615 := by
    simpa [prefixWord, tailWord_1420615, baseEnd_1420615] using wordTrace_append hprefix tailTrace_1420615
  have hstable : (prefixWord ++ tailWord_1420615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420615).length < 2 ^ (prefixWord ++ tailWord_1420615).sum := by decide
  have hdescent : baseEnd_1420615 < baseStart_1420615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420621 : List Nat := [1, 6, 1, 3, 2, 1, 7]
def baseStart_1420621 : Nat := 118140960795 + 1420621 * 2 ^ 59
def prefixEnd_1420621 : Nat := 4983230072969 + 3 ^ 40 * 1420621 * 2
def baseEnd_1420621 : Nat := 36022785228197113456997

theorem tailTrace_1420621 : CollatzResearch.WordTrace tailWord_1420621 prefixEnd_1420621 36022785228197113456997 := by
  unfold tailWord_1420621
  simp only [CollatzResearch.WordTrace]
  refine ⟨51814304586340214595725717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34542869724226809730483811 51814304586340214595725717)
  ·
    refine ⟨2428795527484697559174643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51814304586340214595725717 2428795527484697559174643)
    ·
      refine ⟨3643193291227046338761965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2428795527484697559174643 3643193291227046338761965)
      ·
        refine ⟨1366197484210142377035737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3643193291227046338761965 1366197484210142377035737)
        ·
          refine ⟨1024648113157606782776803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1366197484210142377035737 1024648113157606782776803)
          ·
            refine ⟨1536972169736410174165205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024648113157606782776803 1536972169736410174165205)
            ·
              refine ⟨36022785228197113456997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1536972169736410174165205 36022785228197113456997)
              ·
                rfl

theorem cell21_1420621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 7].length) (baseStart_1420621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420621 prefixEnd_1420621 := by exact prefixLift 1420621
  have htrace : WordTrace (prefixWord ++ tailWord_1420621) baseStart_1420621 baseEnd_1420621 := by
    simpa [prefixWord, tailWord_1420621, baseEnd_1420621] using wordTrace_append hprefix tailTrace_1420621
  have hstable : (prefixWord ++ tailWord_1420621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420621).length < 2 ^ (prefixWord ++ tailWord_1420621).sum := by decide
  have hdescent : baseEnd_1420621 < baseStart_1420621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420804 : List Nat := [2, 3, 2, 3, 2, 1, 3, 2, 3]
def baseStart_1420804 : Nat := 118140960795 + 1420804 * 2 ^ 59
def prefixEnd_1420804 : Nat := 4983230072969 + 3 ^ 40 * 1420804 * 2
def baseEnd_1420804 : Nat := 324246830147006369562599

theorem tailTrace_1420804 : CollatzResearch.WordTrace tailWord_1420804 prefixEnd_1420804 324246830147006369562599 := by
  unfold tailWord_1420804
  simp only [CollatzResearch.WordTrace]
  refine ⟨25910489572338618424818733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34547319429784824566424977 25910489572338618424818733)
  ·
    refine ⟨9716433589626981909307025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25910489572338618424818733 9716433589626981909307025)
    ·
      refine ⟨7287325192220236431980269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9716433589626981909307025 7287325192220236431980269)
      ·
        refine ⟨2732746947082588661992601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7287325192220236431980269 2732746947082588661992601)
        ·
          refine ⟨2049560210311941496494451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732746947082588661992601 2049560210311941496494451)
          ·
            refine ⟨3074340315467912244741677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049560210311941496494451 3074340315467912244741677)
            ·
              refine ⟨1152877618300467091778129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3074340315467912244741677 1152877618300467091778129)
              ·
                refine ⟨864658213725350318833597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152877618300467091778129 864658213725350318833597)
                ·
                  refine ⟨324246830147006369562599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864658213725350318833597 324246830147006369562599)
                  ·
                    rfl

theorem cell21_1420804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_1420804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420804 prefixEnd_1420804 := by exact prefixLift 1420804
  have htrace : WordTrace (prefixWord ++ tailWord_1420804) baseStart_1420804 baseEnd_1420804 := by
    simpa [prefixWord, tailWord_1420804, baseEnd_1420804] using wordTrace_append hprefix tailTrace_1420804
  have hstable : (prefixWord ++ tailWord_1420804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420804).length < 2 ^ (prefixWord ++ tailWord_1420804).sum := by decide
  have hdescent : baseEnd_1420804 < baseStart_1420804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420857 : List Nat := [1, 2, 1, 5, 1, 11]
def baseStart_1420857 : Nat := 118140960795 + 1420857 * 2 ^ 59
def prefixEnd_1420857 : Nat := 4983230072969 + 3 ^ 40 * 1420857 * 2
def baseEnd_1420857 : Nat := 12009589832188520562191

theorem tailTrace_1420857 : CollatzResearch.WordTrace tailWord_1420857 prefixEnd_1420857 12009589832188520562191 := by
  unfold tailWord_1420857
  simp only [CollatzResearch.WordTrace]
  refine ⟨51822912213485226901316825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34548608142323484600877883 51822912213485226901316825)
  ·
    refine ⟨38867184160113920175987619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51822912213485226901316825 38867184160113920175987619)
    ·
      refine ⟨58300776240170880263981429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38867184160113920175987619 58300776240170880263981429)
      ·
        refine ⟨5465697772516020024748259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58300776240170880263981429 5465697772516020024748259)
        ·
          refine ⟨8198546658774030037122389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5465697772516020024748259 8198546658774030037122389)
          ·
            refine ⟨12009589832188520562191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8198546658774030037122389 12009589832188520562191)
            ·
              rfl

theorem cell21_1420857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 11].length) (baseStart_1420857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420857 prefixEnd_1420857 := by exact prefixLift 1420857
  have htrace : WordTrace (prefixWord ++ tailWord_1420857) baseStart_1420857 baseEnd_1420857 := by
    simpa [prefixWord, tailWord_1420857, baseEnd_1420857] using wordTrace_append hprefix tailTrace_1420857
  have hstable : (prefixWord ++ tailWord_1420857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420857).length < 2 ^ (prefixWord ++ tailWord_1420857).sum := by decide
  have hdescent : baseEnd_1420857 < baseStart_1420857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420863 : List Nat := [1, 1, 2, 2, 3, 5, 2, 2, 3]
def baseStart_1420863 : Nat := 118140960795 + 1420863 * 2 ^ 59
def prefixEnd_1420863 : Nat := 4983230072969 + 3 ^ 40 * 1420863 * 2
def baseEnd_1420863 : Nat := 324260294750835378079145

theorem tailTrace_1420863 : CollatzResearch.WordTrace tailWord_1420863 prefixEnd_1420863 324260294750835378079145 := by
  unfold tailWord_1420863
  simp only [CollatzResearch.WordTrace]
  refine ⟨51823131051463489926035243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34548754034308993284023495 51823131051463489926035243)
  ·
    refine ⟨77734696577195234889052865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51823131051463489926035243 77734696577195234889052865)
    ·
      refine ⟨58301022432896426166789649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77734696577195234889052865 58301022432896426166789649)
      ·
        refine ⟨43725766824672319625092237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58301022432896426166789649 43725766824672319625092237)
        ·
          refine ⟨16397162559252119859409589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43725766824672319625092237 16397162559252119859409589)
          ·
            refine ⟨1537233989929886236819649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16397162559252119859409589 1537233989929886236819649)
            ·
              refine ⟨1152925492447414677614737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537233989929886236819649 1152925492447414677614737)
              ·
                refine ⟨864694119335561008211053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152925492447414677614737 864694119335561008211053)
                ·
                  refine ⟨324260294750835378079145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864694119335561008211053 324260294750835378079145)
                  ·
                    rfl

theorem cell21_1420863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 3].length) (baseStart_1420863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420863 prefixEnd_1420863 := by exact prefixLift 1420863
  have htrace : WordTrace (prefixWord ++ tailWord_1420863) baseStart_1420863 baseEnd_1420863 := by
    simpa [prefixWord, tailWord_1420863, baseEnd_1420863] using wordTrace_append hprefix tailTrace_1420863
  have hstable : (prefixWord ++ tailWord_1420863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420863).length < 2 ^ (prefixWord ++ tailWord_1420863).sum := by decide
  have hdescent : baseEnd_1420863 < baseStart_1420863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420905 : List Nat := [1, 2, 1, 1, 1, 4, 3, 5, 3]
def baseStart_1420905 : Nat := 118140960795 + 1420905 * 2 ^ 59
def prefixEnd_1420905 : Nat := 4983230072969 + 3 ^ 40 * 1420905 * 2
def baseEnd_1420905 : Nat := 324269879723052638379059

theorem tailTrace_1420905 : CollatzResearch.WordTrace tailWord_1420905 prefixEnd_1420905 324269879723052638379059 := by
  unfold tailWord_1420905
  simp only [CollatzResearch.WordTrace]
  refine ⟨51824662917311331099064169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34549775278207554066042779 51824662917311331099064169)
  ·
    refine ⟨38868497187983498324298127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51824662917311331099064169 38868497187983498324298127)
    ·
      refine ⟨58302745781975247486447191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38868497187983498324298127 58302745781975247486447191)
      ·
        refine ⟨87454118672962871229670787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58302745781975247486447191 87454118672962871229670787)
        ·
          refine ⟨131181178009444306844506181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87454118672962871229670787 131181178009444306844506181)
          ·
            refine ⟨24596470876770807533344909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131181178009444306844506181 24596470876770807533344909)
            ·
              refine ⟨9223676578789052825004341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24596470876770807533344909 9223676578789052825004341)
              ·
                refine ⟨864719679261473702344157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9223676578789052825004341 864719679261473702344157)
                ·
                  refine ⟨324269879723052638379059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864719679261473702344157 324269879723052638379059)
                  ·
                    rfl

theorem cell21_1420905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_1420905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420905 prefixEnd_1420905 := by exact prefixLift 1420905
  have htrace : WordTrace (prefixWord ++ tailWord_1420905) baseStart_1420905 baseEnd_1420905 := by
    simpa [prefixWord, tailWord_1420905, baseEnd_1420905] using wordTrace_append hprefix tailTrace_1420905
  have hstable : (prefixWord ++ tailWord_1420905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420905).length < 2 ^ (prefixWord ++ tailWord_1420905).sum := by decide
  have hdescent : baseEnd_1420905 < baseStart_1420905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420933 : List Nat := [1, 3, 1, 1, 4, 1, 2, 8]
def baseStart_1420933 : Nat := 118140960795 + 1420933 * 2 ^ 59
def prefixEnd_1420933 : Nat := 4983230072969 + 3 ^ 40 * 1420933 * 2
def baseEnd_1420933 : Nat := 108092089901510270637445

theorem tailTrace_1420933 : CollatzResearch.WordTrace tailWord_1420933 prefixEnd_1420933 108092089901510270637445 := by
  unfold tailWord_1420933
  simp only [CollatzResearch.WordTrace]
  refine ⟨51825684161209891881083453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34550456107473261254055635 51825684161209891881083453)
  ·
    refine ⟨19434631560453709455406295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51825684161209891881083453 19434631560453709455406295)
    ·
      refine ⟨29151947340680564183109443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19434631560453709455406295 29151947340680564183109443)
      ·
        refine ⟨43727921011020846274664165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29151947340680564183109443 43727921011020846274664165)
        ·
          refine ⟨8198985189566408676499531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43727921011020846274664165 8198985189566408676499531)
          ·
            refine ⟨12298477784349613014749297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8198985189566408676499531 12298477784349613014749297)
            ·
              refine ⟨9223858338262209761061973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12298477784349613014749297 9223858338262209761061973)
              ·
                refine ⟨108092089901510270637445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9223858338262209761061973 108092089901510270637445)
                ·
                  rfl

theorem cell21_1420933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 8].length) (baseStart_1420933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420933 prefixEnd_1420933 := by exact prefixLift 1420933
  have htrace : WordTrace (prefixWord ++ tailWord_1420933) baseStart_1420933 baseEnd_1420933 := by
    simpa [prefixWord, tailWord_1420933, baseEnd_1420933] using wordTrace_append hprefix tailTrace_1420933
  have hstable : (prefixWord ++ tailWord_1420933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420933).length < 2 ^ (prefixWord ++ tailWord_1420933).sum := by decide
  have hdescent : baseEnd_1420933 < baseStart_1420933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420956 : List Nat := [2, 2, 3, 2, 4, 1, 1, 3, 3]
def baseStart_1420956 : Nat := 118140960795 + 1420956 * 2 ^ 59
def prefixEnd_1420956 : Nat := 4983230072969 + 3 ^ 40 * 1420956 * 2
def baseEnd_1420956 : Nat := 324281518617887883028955

theorem tailTrace_1420956 : CollatzResearch.WordTrace tailWord_1420956 prefixEnd_1420956 324281518617887883028955 := by
  unfold tailWord_1420956
  simp only [CollatzResearch.WordTrace]
  refine ⟨25913261520063283404585361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34551015360084377872780481 25913261520063283404585361)
  ·
    refine ⟨19434946140047462553439021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25913261520063283404585361 19434946140047462553439021)
    ·
      refine ⟨7288104802517798457539633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19434946140047462553439021 7288104802517798457539633)
      ·
        refine ⟨5466078601888348843154725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7288104802517798457539633 5466078601888348843154725)
        ·
          refine ⟨1024889737854065408091511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5466078601888348843154725 1024889737854065408091511)
          ·
            refine ⟨1537334606781098112137267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024889737854065408091511 1537334606781098112137267)
            ·
              refine ⟨2306001910171647168205901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537334606781098112137267 2306001910171647168205901)
              ·
                refine ⟨864750716314367688077213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2306001910171647168205901 864750716314367688077213)
                ·
                  refine ⟨324281518617887883028955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864750716314367688077213 324281518617887883028955)
                  ·
                    rfl

theorem cell21_1420956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_1420956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1420956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1420956 prefixEnd_1420956 := by exact prefixLift 1420956
  have htrace : WordTrace (prefixWord ++ tailWord_1420956) baseStart_1420956 baseEnd_1420956 := by
    simpa [prefixWord, tailWord_1420956, baseEnd_1420956] using wordTrace_append hprefix tailTrace_1420956
  have hstable : (prefixWord ++ tailWord_1420956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420956).length < 2 ^ (prefixWord ++ tailWord_1420956).sum := by decide
  have hdescent : baseEnd_1420956 < baseStart_1420956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421009 : List Nat := [1, 2, 2, 1, 2, 4, 2, 7]
def baseStart_1421009 : Nat := 118140960795 + 1421009 * 2 ^ 59
def prefixEnd_1421009 : Nat := 4983230072969 + 3 ^ 40 * 1421009 * 2
def baseEnd_1421009 : Nat := 108097871313323856215171

theorem tailTrace_1421009 : CollatzResearch.WordTrace tailWord_1421009 prefixEnd_1421009 108097871313323856215171 := by
  unfold tailWord_1421009
  simp only [CollatzResearch.WordTrace]
  refine ⟨51828456108934556860850081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34552304072623037907233387 51828456108934556860850081)
  ·
    refine ⟨38871342081700917645637561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51828456108934556860850081 38871342081700917645637561)
    ·
      refine ⟨29153506561275688234228171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38871342081700917645637561 29153506561275688234228171)
      ·
        refine ⟨43730259841913532351342257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29153506561275688234228171 43730259841913532351342257)
        ·
          refine ⟨32797694881435149263506693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43730259841913532351342257 32797694881435149263506693)
          ·
            refine ⟨6149567790269090486907505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32797694881435149263506693 6149567790269090486907505)
            ·
              refine ⟨4612175842701817865180629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6149567790269090486907505 4612175842701817865180629)
              ·
                refine ⟨108097871313323856215171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4612175842701817865180629 108097871313323856215171)
                ·
                  rfl

theorem cell21_1421009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 7].length) (baseStart_1421009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421009 prefixEnd_1421009 := by exact prefixLift 1421009
  have htrace : WordTrace (prefixWord ++ tailWord_1421009) baseStart_1421009 baseEnd_1421009 := by
    simpa [prefixWord, tailWord_1421009, baseEnd_1421009] using wordTrace_append hprefix tailTrace_1421009
  have hstable : (prefixWord ++ tailWord_1421009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421009).length < 2 ^ (prefixWord ++ tailWord_1421009).sum := by decide
  have hdescent : baseEnd_1421009 < baseStart_1421009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421116 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_1421116 : Nat := 118140960795 + 1421116 * 2 ^ 59
def prefixEnd_1421116 : Nat := 4983230072969 + 3 ^ 40 * 1421116 * 2
def baseEnd_1421116 : Nat := 324318032797763160361961

theorem tailTrace_1421116 : CollatzResearch.WordTrace tailWord_1421116 prefixEnd_1421116 324318032797763160361961 := by
  unfold tailWord_1421116
  simp only [CollatzResearch.WordTrace]
  refine ⟨25916179359773457067497601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34554905813031276089996801 25916179359773457067497601)
  ·
    refine ⟨19437134519830092800623201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25916179359773457067497601 19437134519830092800623201)
    ·
      refine ⟨14577850889872569600467401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19437134519830092800623201 14577850889872569600467401)
      ·
        refine ⟨10933388167404427200350551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14577850889872569600467401 10933388167404427200350551)
        ·
          refine ⟨16400082251106640800525827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10933388167404427200350551 16400082251106640800525827)
          ·
            refine ⟨24600123376659961200788741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16400082251106640800525827 24600123376659961200788741)
            ·
              refine ⟨4612523133123742725147889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24600123376659961200788741 4612523133123742725147889)
              ·
                refine ⟨3459392349842807043860917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4612523133123742725147889 3459392349842807043860917)
                ·
                  refine ⟨324318032797763160361961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3459392349842807043860917 324318032797763160361961)
                  ·
                    rfl

theorem cell21_1421116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_1421116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421116 prefixEnd_1421116 := by exact prefixLift 1421116
  have htrace : WordTrace (prefixWord ++ tailWord_1421116) baseStart_1421116 baseEnd_1421116 := by
    simpa [prefixWord, tailWord_1421116, baseEnd_1421116] using wordTrace_append hprefix tailTrace_1421116
  have hstable : (prefixWord ++ tailWord_1421116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421116).length < 2 ^ (prefixWord ++ tailWord_1421116).sum := by decide
  have hdescent : baseEnd_1421116 < baseStart_1421116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421119 : List Nat := [1, 1, 2, 2, 6, 2, 2, 5]
def baseStart_1421119 : Nat := 118140960795 + 1421119 * 2 ^ 59
def prefixEnd_1421119 : Nat := 4983230072969 + 3 ^ 40 * 1421119 * 2
def baseEnd_1421119 : Nat := 108106239146211940603985

theorem tailTrace_1421119 : CollatzResearch.WordTrace tailWord_1421119 prefixEnd_1421119 108106239146211940603985 := by
  unfold tailWord_1421119
  simp only [CollatzResearch.WordTrace]
  refine ⟨51832468138536045647354411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34554978759024030431569607 51832468138536045647354411)
  ·
    refine ⟨77748702207804068471031617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51832468138536045647354411 77748702207804068471031617)
    ·
      refine ⟨58311526655853051353273713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77748702207804068471031617 58311526655853051353273713)
      ·
        refine ⟨43733644991889788514955285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58311526655853051353273713 43733644991889788514955285)
        ·
          refine ⟨2050014608994833836638529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43733644991889788514955285 2050014608994833836638529)
          ·
            refine ⟨1537510956746125377478897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2050014608994833836638529 1537510956746125377478897)
            ·
              refine ⟨1153133217559594033109173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537510956746125377478897 1153133217559594033109173)
              ·
                refine ⟨108106239146211940603985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1153133217559594033109173 108106239146211940603985)
                ·
                  rfl

theorem cell21_1421119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 5].length) (baseStart_1421119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421119 prefixEnd_1421119 := by exact prefixLift 1421119
  have htrace : WordTrace (prefixWord ++ tailWord_1421119) baseStart_1421119 baseEnd_1421119 := by
    simpa [prefixWord, tailWord_1421119, baseEnd_1421119] using wordTrace_append hprefix tailTrace_1421119
  have hstable : (prefixWord ++ tailWord_1421119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421119).length < 2 ^ (prefixWord ++ tailWord_1421119).sum := by decide
  have hdescent : baseEnd_1421119 < baseStart_1421119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421130 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1421130 : Nat := 118140960795 + 1421130 * 2 ^ 59
def prefixEnd_1421130 : Nat := 4983230072969 + 3 ^ 40 * 1421130 * 2
def baseEnd_1421130 : Nat := 324321227788502247128599

theorem tailTrace_1421130 : CollatzResearch.WordTrace tailWord_1421130 prefixEnd_1421130 324321227788502247128599 := by
  unfold tailWord_1421130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12958217335374048631501211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34555246227664129684003229 12958217335374048631501211)
  ·
    refine ⟨19437326003061072947251817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12958217335374048631501211 19437326003061072947251817)
    ·
      refine ⟨14577994502295804710438863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19437326003061072947251817 14577994502295804710438863)
      ·
        refine ⟨21866991753443707065658295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14577994502295804710438863 21866991753443707065658295)
        ·
          refine ⟨32800487630165560598487443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21866991753443707065658295 32800487630165560598487443)
          ·
            refine ⟨49200731445248340897731165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32800487630165560598487443 49200731445248340897731165)
            ·
              refine ⟨18450274291968127836649187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49200731445248340897731165 18450274291968127836649187)
              ·
                refine ⟨27675411437952191754973781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18450274291968127836649187 27675411437952191754973781)
                ·
                  refine ⟨324321227788502247128599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27675411437952191754973781 324321227788502247128599)
                  ·
                    rfl

theorem cell21_1421130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1421130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421130 prefixEnd_1421130 := by exact prefixLift 1421130
  have htrace : WordTrace (prefixWord ++ tailWord_1421130) baseStart_1421130 baseEnd_1421130 := by
    simpa [prefixWord, tailWord_1421130, baseEnd_1421130] using wordTrace_append hprefix tailTrace_1421130
  have hstable : (prefixWord ++ tailWord_1421130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421130).length < 2 ^ (prefixWord ++ tailWord_1421130).sum := by decide
  have hdescent : baseEnd_1421130 < baseStart_1421130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421164 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_1421164 : Nat := 118140960795 + 1421164 * 2 ^ 59
def prefixEnd_1421164 : Nat := 4983230072969 + 3 ^ 40 * 1421164 * 2
def baseEnd_1421164 : Nat := 324328987051725743561863

theorem tailTrace_1421164 : CollatzResearch.WordTrace tailWord_1421164 prefixEnd_1421164 324328987051725743561863 := by
  unfold tailWord_1421164
  simp only [CollatzResearch.WordTrace]
  refine ⟨25917054711686509166371273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34556072948915345555161697 25917054711686509166371273)
  ·
    refine ⟨19437791033764881874778455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25917054711686509166371273 19437791033764881874778455)
    ·
      refine ⟨29156686550647322812167683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19437791033764881874778455 29156686550647322812167683)
      ·
        refine ⟨43735029825970984218251525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29156686550647322812167683 43735029825970984218251525)
        ·
          refine ⟨8200318092369559540922161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43735029825970984218251525 8200318092369559540922161)
          ·
            refine ⟨6150238569277169655691621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8200318092369559540922161 6150238569277169655691621)
            ·
              refine ⟨1153169731739469310442179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6150238569277169655691621 1153169731739469310442179)
              ·
                refine ⟨1729754597609203965663269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153169731739469310442179 1729754597609203965663269)
                ·
                  refine ⟨324328987051725743561863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729754597609203965663269 324328987051725743561863)
                  ·
                    rfl

theorem cell21_1421164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_1421164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421164 prefixEnd_1421164 := by exact prefixLift 1421164
  have htrace : WordTrace (prefixWord ++ tailWord_1421164) baseStart_1421164 baseEnd_1421164 := by
    simpa [prefixWord, tailWord_1421164, baseEnd_1421164] using wordTrace_append hprefix tailTrace_1421164
  have hstable : (prefixWord ++ tailWord_1421164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421164).length < 2 ^ (prefixWord ++ tailWord_1421164).sum := by decide
  have hdescent : baseEnd_1421164 < baseStart_1421164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421333 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 4]
def baseStart_1421333 : Nat := 118140960795 + 1421333 * 2 ^ 59
def prefixEnd_1421333 : Nat := 4983230072969 + 3 ^ 40 * 1421333 * 2
def baseEnd_1421333 : Nat := 324367555154219005244851

theorem tailTrace_1421333 : CollatzResearch.WordTrace tailWord_1421333 prefixEnd_1421333 324367555154219005244851 := by
  unfold tailWord_1421333
  simp only [CollatzResearch.WordTrace]
  refine ⟨51840273359760760195644653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34560182239840506797096435 51840273359760760195644653)
  ·
    refine ⟨19440102509910285073366745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51840273359760760195644653 19440102509910285073366745)
    ·
      refine ⟨14580076882432713805025059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19440102509910285073366745 14580076882432713805025059)
      ·
        refine ⟨21870115323649070707537589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14580076882432713805025059 21870115323649070707537589)
        ·
          refine ⟨2050323311592100378831649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21870115323649070707537589 2050323311592100378831649)
          ·
            refine ⟨1537742483694075284123737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2050323311592100378831649 1537742483694075284123737)
            ·
              refine ⟨1153306862770556463092803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537742483694075284123737 1153306862770556463092803)
              ·
                refine ⟨1729960294155834694639205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153306862770556463092803 1729960294155834694639205)
                ·
                  refine ⟨324367555154219005244851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729960294155834694639205 324367555154219005244851)
                  ·
                    rfl

theorem cell21_1421333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_1421333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421333 prefixEnd_1421333 := by exact prefixLift 1421333
  have htrace : WordTrace (prefixWord ++ tailWord_1421333) baseStart_1421333 baseEnd_1421333 := by
    simpa [prefixWord, tailWord_1421333, baseEnd_1421333] using wordTrace_append hprefix tailTrace_1421333
  have hstable : (prefixWord ++ tailWord_1421333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421333).length < 2 ^ (prefixWord ++ tailWord_1421333).sum := by decide
  have hdescent : baseEnd_1421333 < baseStart_1421333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421437 : List Nat := [1, 4, 1, 1, 3, 2, 2, 4, 3]
def baseStart_1421437 : Nat := 118140960795 + 1421437 * 2 ^ 59
def prefixEnd_1421437 : Nat := 4983230072969 + 3 ^ 40 * 1421437 * 2
def baseEnd_1421437 : Nat := 324391289371137935511305

theorem tailTrace_1421437 : CollatzResearch.WordTrace tailWord_1421437 prefixEnd_1421437 324391289371137935511305 := by
  unfold tailWord_1421437
  simp only [CollatzResearch.WordTrace]
  refine ⟨51844066551383985957430565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34562711034255990638287043 51844066551383985957430565)
  ·
    refine ⟨9720762478384497367018231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51844066551383985957430565 9720762478384497367018231)
    ·
      refine ⟨14581143717576746050527347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9720762478384497367018231 14581143717576746050527347)
      ·
        refine ⟨21871715576365119075791021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14581143717576746050527347 21871715576365119075791021)
        ·
          refine ⟨8201893341136919653421633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21871715576365119075791021 8201893341136919653421633)
          ·
            refine ⟨6151420005852689740066225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8201893341136919653421633 6151420005852689740066225)
            ·
              refine ⟨4613565004389517305049669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6151420005852689740066225 4613565004389517305049669)
              ·
                refine ⟨865043438323034494696813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4613565004389517305049669 865043438323034494696813)
                ·
                  refine ⟨324391289371137935511305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865043438323034494696813 324391289371137935511305)
                  ·
                    rfl

theorem cell21_1421437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_1421437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421437 prefixEnd_1421437 := by exact prefixLift 1421437
  have htrace : WordTrace (prefixWord ++ tailWord_1421437) baseStart_1421437 baseEnd_1421437 := by
    simpa [prefixWord, tailWord_1421437, baseEnd_1421437] using wordTrace_append hprefix tailTrace_1421437
  have hstable : (prefixWord ++ tailWord_1421437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421437).length < 2 ^ (prefixWord ++ tailWord_1421437).sum := by decide
  have hdescent : baseEnd_1421437 < baseStart_1421437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421502 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1421502 : Nat := 118140960795 + 1421502 * 2 ^ 59
def prefixEnd_1421502 : Nat := 4983230072969 + 3 ^ 40 * 1421502 * 2
def baseEnd_1421502 : Nat := 324406123256712266927839

theorem tailTrace_1421502 : CollatzResearch.WordTrace tailWord_1421502 prefixEnd_1421502 324406123256712266927839 := by
  unfold tailWord_1421502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6480804662018562757318345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34564291530765668039031173 6480804662018562757318345)
  ·
    refine ⟨4860603496513922067988759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6480804662018562757318345 4860603496513922067988759)
    ·
      refine ⟨7290905244770883101983139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4860603496513922067988759 7290905244770883101983139)
      ·
        refine ⟨10936357867156324652974709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7290905244770883101983139 10936357867156324652974709)
        ·
          refine ⟨1025283550045905436216379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10936357867156324652974709 1025283550045905436216379)
          ·
            refine ⟨1537925325068858154324569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025283550045905436216379 1537925325068858154324569)
            ·
              refine ⟨1153443993801643615743427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537925325068858154324569 1153443993801643615743427)
              ·
                refine ⟨1730165990702465423615141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153443993801643615743427 1730165990702465423615141)
                ·
                  refine ⟨324406123256712266927839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1730165990702465423615141 324406123256712266927839)
                  ·
                    rfl

theorem cell21_1421502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1421502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421502 prefixEnd_1421502 := by exact prefixLift 1421502
  have htrace : WordTrace (prefixWord ++ tailWord_1421502) baseStart_1421502 baseEnd_1421502 := by
    simpa [prefixWord, tailWord_1421502, baseEnd_1421502] using wordTrace_append hprefix tailTrace_1421502
  have hstable : (prefixWord ++ tailWord_1421502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421502).length < 2 ^ (prefixWord ++ tailWord_1421502).sum := by decide
  have hdescent : baseEnd_1421502 < baseStart_1421502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421555 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 5]
def baseStart_1421555 : Nat := 118140960795 + 1421555 * 2 ^ 59
def prefixEnd_1421555 : Nat := 4983230072969 + 3 ^ 40 * 1421555 * 2
def baseEnd_1421555 : Nat := 324418218578795952544397

theorem tailTrace_1421555 : CollatzResearch.WordTrace tailWord_1421555 prefixEnd_1421555 324418218578795952544397 := by
  unfold tailWord_1421555
  simp only [CollatzResearch.WordTrace]
  refine ⟨51848370364956492110226119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34565580243304328073484079 51848370364956492110226119)
  ·
    refine ⟨77772555547434738165339179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51848370364956492110226119 77772555547434738165339179)
    ·
      refine ⟨116658833321152107248008769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77772555547434738165339179 116658833321152107248008769)
      ·
        refine ⟨87494124990864080436006577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116658833321152107248008769 87494124990864080436006577)
        ·
          refine ⟨65620593743148060327004933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87494124990864080436006577 65620593743148060327004933)
          ·
            refine ⟨12303861326840261311313425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65620593743148060327004933 12303861326840261311313425)
            ·
              refine ⟨9227895995130195983485069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12303861326840261311313425 9227895995130195983485069)
              ·
                refine ⟨3460460998173823493806901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9227895995130195983485069 3460460998173823493806901)
                ·
                  refine ⟨324418218578795952544397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3460460998173823493806901 324418218578795952544397)
                  ·
                    rfl

theorem cell21_1421555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_1421555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421555 prefixEnd_1421555 := by exact prefixLift 1421555
  have htrace : WordTrace (prefixWord ++ tailWord_1421555) baseStart_1421555 baseEnd_1421555 := by
    simpa [prefixWord, tailWord_1421555, baseEnd_1421555] using wordTrace_append hprefix tailTrace_1421555
  have hstable : (prefixWord ++ tailWord_1421555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421555).length < 2 ^ (prefixWord ++ tailWord_1421555).sum := by decide
  have hdescent : baseEnd_1421555 < baseStart_1421555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421575 : List Nat := [1, 1, 4, 5, 1, 1, 3, 5]
def baseStart_1421575 : Nat := 118140960795 + 1421575 * 2 ^ 59
def prefixEnd_1421575 : Nat := 4983230072969 + 3 ^ 40 * 1421575 * 2
def baseEnd_1421575 : Nat := 108140927617093454070341

theorem tailTrace_1421575 : CollatzResearch.WordTrace tailWord_1421575 prefixEnd_1421575 108140927617093454070341 := by
  unfold tailWord_1421575
  simp only [CollatzResearch.WordTrace]
  refine ⟨51849099824884035525954179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34566066549922690350636119 51849099824884035525954179)
  ·
    refine ⟨77773649737326053288931269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51849099824884035525954179 77773649737326053288931269)
    ·
      refine ⟨14582559325748634991674613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77773649737326053288931269 14582559325748634991674613)
      ·
        refine ⟨1367114936788934530469495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14582559325748634991674613 1367114936788934530469495)
        ·
          refine ⟨2050672405183401795704243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367114936788934530469495 2050672405183401795704243)
          ·
            refine ⟨3076008607775102693556365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050672405183401795704243 3076008607775102693556365)
            ·
              refine ⟨1153503227915663510083637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3076008607775102693556365 1153503227915663510083637)
              ·
                refine ⟨108140927617093454070341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1153503227915663510083637 108140927617093454070341)
                ·
                  rfl

theorem cell21_1421575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 5].length) (baseStart_1421575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421575 prefixEnd_1421575 := by exact prefixLift 1421575
  have htrace : WordTrace (prefixWord ++ tailWord_1421575) baseStart_1421575 baseEnd_1421575 := by
    simpa [prefixWord, tailWord_1421575, baseEnd_1421575] using wordTrace_append hprefix tailTrace_1421575
  have hstable : (prefixWord ++ tailWord_1421575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421575).length < 2 ^ (prefixWord ++ tailWord_1421575).sum := by decide
  have hdescent : baseEnd_1421575 < baseStart_1421575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421631 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 5]
def baseStart_1421631 : Nat := 118140960795 + 1421631 * 2 ^ 59
def prefixEnd_1421631 : Nat := 4983230072969 + 3 ^ 40 * 1421631 * 2
def baseEnd_1421631 : Nat := 324435562814236709277575

theorem tailTrace_1421631 : CollatzResearch.WordTrace tailWord_1421631 prefixEnd_1421631 324435562814236709277575 := by
  unfold tailWord_1421631
  simp only [CollatzResearch.WordTrace]
  refine ⟨51851142312681157089992747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34567428208454104726661831 51851142312681157089992747)
  ·
    refine ⟨77776713469021735634989121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51851142312681157089992747 77776713469021735634989121)
    ·
      refine ⟨58332535101766301726241841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77776713469021735634989121 58332535101766301726241841)
      ·
        refine ⟨43749401326324726294681381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58332535101766301726241841 43749401326324726294681381)
        ·
          refine ⟨8203012748685886180252759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43749401326324726294681381 8203012748685886180252759)
          ·
            refine ⟨12304519123028829270379139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8203012748685886180252759 12304519123028829270379139)
            ·
              refine ⟨18456778684543243905568709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12304519123028829270379139 18456778684543243905568709)
              ·
                refine ⟨3460646003351858232294133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18456778684543243905568709 3460646003351858232294133)
                ·
                  refine ⟨324435562814236709277575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3460646003351858232294133 324435562814236709277575)
                  ·
                    rfl

theorem cell21_1421631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_1421631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421631 prefixEnd_1421631 := by exact prefixLift 1421631
  have htrace : WordTrace (prefixWord ++ tailWord_1421631) baseStart_1421631 baseEnd_1421631 := by
    simpa [prefixWord, tailWord_1421631, baseEnd_1421631] using wordTrace_append hprefix tailTrace_1421631
  have hstable : (prefixWord ++ tailWord_1421631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421631).length < 2 ^ (prefixWord ++ tailWord_1421631).sum := by decide
  have hdescent : baseEnd_1421631 < baseStart_1421631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421716 : List Nat := [2, 4, 2, 1, 4, 1, 2, 2, 3]
def baseStart_1421716 : Nat := 118140960795 + 1421716 * 2 ^ 59
def prefixEnd_1421716 : Nat := 4983230072969 + 3 ^ 40 * 1421716 * 2
def baseEnd_1421716 : Nat := 324454960972295450360735

theorem tailTrace_1421716 : CollatzResearch.WordTrace tailWord_1421716 prefixEnd_1421716 324454960972295450360735 := by
  unfold tailWord_1421716
  simp only [CollatzResearch.WordTrace]
  refine ⟨25927121258686608303418501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34569495011582144404558001 25927121258686608303418501)
  ·
    refine ⟨4861335236003739056890969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25927121258686608303418501 4861335236003739056890969)
    ·
      refine ⟨3646001427002804292668227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4861335236003739056890969 3646001427002804292668227)
      ·
        refine ⟨5469002140504206439002341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3646001427002804292668227 5469002140504206439002341)
        ·
          refine ⟨1025437901344538707312939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5469002140504206439002341 1025437901344538707312939)
          ·
            refine ⟨1538156852016808060969409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025437901344538707312939 1538156852016808060969409)
            ·
              refine ⟨1153617639012606045727057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538156852016808060969409 1153617639012606045727057)
              ·
                refine ⟨865213229259454534295293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153617639012606045727057 865213229259454534295293)
                ·
                  refine ⟨324454960972295450360735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865213229259454534295293 324454960972295450360735)
                  ·
                    rfl

theorem cell21_1421716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_1421716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421716 prefixEnd_1421716 := by exact prefixLift 1421716
  have htrace : WordTrace (prefixWord ++ tailWord_1421716) baseStart_1421716 baseEnd_1421716 := by
    simpa [prefixWord, tailWord_1421716, baseEnd_1421716] using wordTrace_append hprefix tailTrace_1421716
  have hstable : (prefixWord ++ tailWord_1421716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421716).length < 2 ^ (prefixWord ++ tailWord_1421716).sum := by decide
  have hdescent : baseEnd_1421716 < baseStart_1421716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421741 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1421741 : Nat := 118140960795 + 1421741 * 2 ^ 59
def prefixEnd_1421741 : Nat := 4983230072969 + 3 ^ 40 * 1421741 * 2
def baseEnd_1421741 : Nat := 324460666312900962444017

theorem tailTrace_1421741 : CollatzResearch.WordTrace tailWord_1421741 prefixEnd_1421741 324460666312900962444017 := by
  unfold tailWord_1421741
  simp only [CollatzResearch.WordTrace]
  refine ⟨51855154342282645876497077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34570102894855097250998051 51855154342282645876497077)
  ·
    refine ⟨4861420719588998050921601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51855154342282645876497077 4861420719588998050921601)
    ·
      refine ⟨3646065539691748538191201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4861420719588998050921601 3646065539691748538191201)
      ·
        refine ⟨2734549154768811403643401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3646065539691748538191201 2734549154768811403643401)
        ·
          refine ⟨2050911866076608552732551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2734549154768811403643401 2050911866076608552732551)
          ·
            refine ⟨3076367799114912829098827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050911866076608552732551 3076367799114912829098827)
            ·
              refine ⟨4614551698672369243648241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076367799114912829098827 4614551698672369243648241)
              ·
                refine ⟨3460913774004276932736181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614551698672369243648241 3460913774004276932736181)
                ·
                  refine ⟨324460666312900962444017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3460913774004276932736181 324460666312900962444017)
                  ·
                    rfl

theorem cell21_1421741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1421741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421741 prefixEnd_1421741 := by exact prefixLift 1421741
  have htrace : WordTrace (prefixWord ++ tailWord_1421741) baseStart_1421741 baseEnd_1421741 := by
    simpa [prefixWord, tailWord_1421741, baseEnd_1421741] using wordTrace_append hprefix tailTrace_1421741
  have hstable : (prefixWord ++ tailWord_1421741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421741).length < 2 ^ (prefixWord ++ tailWord_1421741).sum := by decide
  have hdescent : baseEnd_1421741 < baseStart_1421741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
